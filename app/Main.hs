module Main where

import Control.Monad.Except (runExcept)

import Bindings.Libtdl  

import Parse (parseScript, parseRepl, parsePreRepl, ReplMessage(..))
import Data
import Interpret.Eval (evalToEither, evalTop, Result(..), runIO)
import Syntax.Core
import Syntax.Macroexpand 
import Syntax.Conversions (toIntermediate,
                           toTIntermediateTop,
                           toCore,
                           toTopCore)
import Typecheck.Typecheck
import Server (startServer)

import System.IO
import Interpret.Lib (defaultStructure)
import qualified Interpret.Environment as Env

import Data.Text (pack)
import qualified Data.Map as Map

-- Parsing Command Line Args
import Options.Applicative
import Data.Semigroup ((<>))

defaultState = ProgState { _uid_counter = 0
                         , _var_counter = 0
                         , _thunk_counter = 0
                         , _thunk_map = Map.empty }

data Mode = Script | Interactive | Compile

data Args = Args { file :: String,
                   mode :: String }

args :: Parser Args
args = Args
  <$> strOption
      (long "file"
      <> value ""
      <> help "The source file of compilation")
  <*> strOption
      (long "mode"
       <> short 'm'
       <> help "What mode to run in: (i)nteractive, (s)erver of (c)ompilation")

main :: IO ()
main = do
  hSetEncoding stdin utf8
  hSetEncoding stdout utf8
  process =<< execParser opts
    where
      opts = info (args <**> helper)
          (fullDesc
          <> progDesc "Compiler for the Modulus programming language"
          <> header "MODULUS")

      process :: Args -> IO ()
      process (Args {file=f, mode=m}) =
        case m of 
          m | m == "c" || m == "compiled" ->
              putStrLn "compilation not implemented yet!"
            | m == "i" || m == "interactive" -> do
              succ <- initModuleLoader 
              if succ then do
                if null f then
                  repl defaultEnv defaultState
                else do
                  handle <- openFile f ReadMode
                  contents <- hGetContents handle
                  (env', state') <- runInteractively contents defaultEnv defaultState
                  repl env' state'
              else
                putStrLn "module loader failed to initialize"
            | m == "s" || m == "server" ->
              startServer defaultState defaultEnv
            | otherwise -> putStrLn "bad mode argument"
  
-- The REPL 
defaultEnv :: Environment 
defaultEnv = Environment
  { localCtx = Map.empty
  , currentModule = NormSct (toEmpty defaultStructure) (NormSig [])
  , globalModule = NormSct [] (NormSig [])
  }


data ReplSettings = ReplSettings { displayTypes :: Bool }

defaultSettings = ReplSettings { displayTypes = False }
  

repl :: Environment -> ProgState -> IO ()
repl env state = repl' env state defaultSettings
  where 
    repl' env state settings = do
      putStr "> "
      hFlush stdout
      line <- getLine
      case parsePreRepl "repl" (pack line) of 
        Left err -> printFlush err >> repl' env state settings
        Right Quit -> pure ()
        Right ToggleType -> repl' env state
          (settings {displayTypes = (not $ displayTypes settings)})
        Right (LoadForeign str) -> do
          mdle <- loadModuleWithErr str
          case mdle of  
            Right v -> printFlush "success!"
            Left err -> printFlush ("failed to load " <> str <> ": " <> err)
          repl' env state  settings
        Right Continue ->
          case parseRepl "stdin" (pack line) of
            Left err -> do
              printFlush err
              repl' env state settings
            Right val -> do
              (env', state') <- runExprs [val] env state settings
              repl' env' state' settings
          


runInteractively :: String -> Environment -> ProgState -> IO (Environment, ProgState)
runInteractively str env state =
  case parseScript "file" (pack str) of
      Left err -> printFlush err >> pure (env, state)
      Right vals -> runExprs vals env state defaultSettings

-- runExprs takes in an AST list, an environment, a state and a flag (whether to
-- run any IO actions encountered)
runExprs :: [AST] -> Environment -> ProgState -> ReplSettings -> IO (Environment, ProgState)
runExprs [] env state _ = pure (env, state)
runExprs (e : es) env state sets = do
  -- result <- evalToIO compile env state 
  -- where my_mnd = do
  --         expanded <- macroExpand e 
  --         intermediate <- liftExcept toIntermediateM e 
  --         tintermediate <- toTIntermediateTop intermediate
  --         env <- ask
  --         checked <- typeCheckTop tintermediate (Ctx.envToCtx env)
  --         core <- liftExcept $ toCore checked
  result <- evalToIO (macroExpand e) env state
  case result of 
    Just (expanded, state') ->
      case toIntermediate expanded env of 
        Right val -> do
          result <- evalToIO (toTIntermediateTop val) env state'
          case result of 
            Just (tint, state'') -> do
              result <- evalToIO (typeCheckTop tint env) env state''
              case result of 
                Just (cint, state''') -> do
                  cint' <- case cint of 
                        Left (t, ty) -> do
                          if (displayTypes sets) then (printFlush ty) else pure ()
                          pure t
                        Right t -> pure t
                  case runExcept (toTopCore cint') of 
                    Right v -> do
                      (fenv, fstate, mval) <- evalTopCore v env state''
                      fstate' <- case mval of 
                        Just mval -> do
                          (val, state) <- runIO mval fenv fstate
                          pure state
                        Nothing -> pure fstate
                      runExprs es fenv fstate' sets
                    Left err -> failWith ("toCore err: " <> err)
                Nothing -> pure (env, state)
            Nothing -> pure (env, state)
        Left err -> do
          printFlush err
          pure (env, state)
    Nothing -> do
      printFlush "macro-expansion err"
      pure (env, state)
  where
    failWith err = (putStrLn err) >> (pure (env, state))

evalTopCore :: TopCore -> Environment -> ProgState -> IO (Environment, ProgState, Maybe Normal)   
evalTopCore core env state = do
  out <- evalToIO (evalTop core) env state
  case out of 
    Just (result, state') -> case result of
      RValue val -> pure (env, state', Just val)
      RDef fnc -> pure (fnc env, state', Nothing)
    Nothing -> pure (env, state, Nothing)
  

printFlush s = print s >> hFlush stdout   


evalToIO v e s = case evalToEither v e s of
  Right val -> pure $ Just val
  Left err -> printFlush err >> pure Nothing

