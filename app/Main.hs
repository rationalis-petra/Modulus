module Main where

import Control.Monad.Except (runExcept)

import Parse (parseScript, parseRepl)
import Data
import Interpret.Eval (evalToIO, evalTop, Result(..), loopAction)
import Syntax.Macroexpand 
import Syntax.Conversions (toIntermediate,
                           toTIntermediateTop,
                           toCore,
                           toTopCore)
import Typecheck.Typecheck
import Server (startServer)


import System.IO
import Interpret.Structures (defaultStructure)
import qualified Interpret.Environment as Env

import Data.Text (pack)
import qualified Data.Map as Map

-- Parsing Command Line Args
import Options.Applicative
import Data.Semigroup ((<>))

defaultState = ProgState { _uid_counter = 0, _var_counter = 0 }  

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
         -- If we are in interpret mode: 
        case m of 
          m | m == "c" || m == "compiled" ->
              putStrLn "compilation not implemented yet!"
            | m == "i" || m == "interactive" ->  do
                dfc <- evalToIO defaultContext (Env.empty) defaultState
                case dfc of
                  Just (env, state) ->
                    if null f then
                      repl env state
                    else do
                      handle <- openFile f ReadMode
                      contents <- hGetContents handle
                      (env', state') <- runInteractively contents env state
                      repl env' state'
                  Nothing -> putStrLn "error in initialisation"
            | m == "s" || m == "server" -> do
                dfc <- evalToIO defaultContext (Env.empty) defaultState
                case dfc of
                  Just (env, state) ->
                    startServer state env
                  Nothing -> putStrLn "error in initialisation"

                
            | otherwise -> putStrLn "bad mode argument"
  
-- The REPL 
defaultContext :: EvalM Environment 
defaultContext = do
  dfm <- defaultStructure
  pure $ Environment {
  localCtx = Map.empty,
  currentModule = NormSct (toEmpty dfm) (NormSig []),
  globalModule = NormSct [] (NormSig [])}


repl :: Environment -> ProgState -> IO ()
repl env state = do
  putStr "> "
  hFlush stdout
  lne <- getLine
  case lne of 
    ":q" -> pure ()
    ":t" -> repl env state
    _ -> do
      case parseRepl "stdin" (pack lne) of
        Left err -> do
          printFlush err
          repl env state 
        Right val -> do
          (env', state') <- runExprs [val] env state True
          repl env' state'
          


runInteractively :: String -> Environment -> ProgState -> IO (Environment, ProgState)
runInteractively str env state =
  case parseScript "file" (pack str) of
      Left err -> printFlush err >> pure (env, state)
      Right vals -> runExprs vals env state False

-- runExprs takes in an AST list, an environment, a state and a flag (whether to
-- run any IO actions encountered)
runExprs :: [AST] -> Environment -> ProgState -> Bool -> IO (Environment, ProgState)
runExprs [] env state _ = pure (env, state)
runExprs (e : es) env state runIO = do
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
                        Left (t, ty) -> (printFlush ty) >> pure t
                        Right t -> pure t
                  case runExcept (toTopCore cint') of 
                    Right v -> do
                      (fenv, fstate, mval) <- evalTopCore v env state''
                      fstate' <- case mval of 
                        Just mval -> do
                          (val, state) <- loopAction mval fenv fstate
                          printFlush val
                          pure state
                        Nothing -> pure fstate
                      runExprs es fenv fstate' runIO
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
