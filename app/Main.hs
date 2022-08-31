module Main where

import Control.Monad.Except (runExcept)

import Parse (parseFile, parseRepl)
import Data
import Interpret.Eval (evalToIO, evalTop)
import Syntax.Macroexpand 
import Syntax.Intermediate (toIntermediate) 
import Syntax.Conversions (toTIntermediateTop, toCore, toTopCore) 
-- import Typecheck.Typecheck

import Typecheck.Typecheck
import qualified Typecheck.Context as Ctx


import System.IO

import Interpret.Structures (defaultStructure)
import qualified Interpret.Environment as Env

import Data.Text (pack)
import qualified Data.Map as Map

  -- Parsing Command Line Args
import Options.Applicative
import Data.Semigroup ((<>))

defaultState = ProgState { _uid_counter = 0, _var_counter = 0 }  

data Args = Args
  { file        :: String,
    interactive :: Bool }

args :: Parser Args
args = Args
  <$> strOption
      (long "file"
      <> value ""
      <> help "The source file of compilation")
  <*> switch
      (long "interactive"
       <> short 'i'
       <> help "Whether to run in interactive mode (REPL)")

main :: IO ()
main =
  process =<< execParser opts
    where
      opts = info (args <**> helper)
          (fullDesc
          <> progDesc "Compiler for the Modulus programming language"
          <> header "MODULUS")

      process :: Args -> IO ()
      process (Args {file=f, interactive=i}) =
         -- If we are in interpret mode: 
         if i then do
           dfc <- evalToIO defaultContext (Env.empty) defaultState
           case dfc of 
             Just (env, state) ->
               if null f then
                 repl env state (IOpts {tc=True})
               else do
                 handle <- openFile f ReadMode
                 contents <- hGetContents handle
                 (env', state') <- runInteractively contents env state (IOpts {tc=False})
                 repl env' state' (IOpts {tc=True})
             Nothing -> 
               putStrLn "error in initialisation"

         -- If we are in compilation mode, then we're expecting  
         else
           putStrLn "compilation not implemented yet!"
  




-- The REPL
  
defaultContext :: EvalM Environment 
defaultContext = do
  dfm <- defaultStructure
  pure $ Environment {
  localCtx = Map.empty,
  currentModule = NormMod dfm,
  globalModule = NormMod [] }

data IOpts = IOpts { tc :: Bool }
  

repl :: Environment -> ProgState -> IOpts -> IO ()
repl env state opts = do
  putStr "> "
  hFlush stdout
  lne <- getLine
  case lne of 
    ":q" -> pure ()
    ":t" -> repl env state (IOpts {tc = not (tc opts)})
    _ -> do
      case parseRepl "stdin" (pack lne) of
        Left err -> do
          -- print err
          print "parse error"
          repl env state opts
        Right val -> do
          (env', state') <- runExprs [val] env state opts True
          repl env' state' opts
          


runInteractively :: String -> Environment -> ProgState -> IOpts
                 -> IO (Environment, ProgState)
runInteractively str env state opts =
  case parseFile "file" (pack str) of
      Left err -> print err >> pure (env, state)
      Right vals -> runExprs vals env state opts False

-- runExprs takes in an AST list, a context
runExprs :: [AST] -> Environment -> ProgState -> IOpts -> Bool
              -> IO (Environment, ProgState)
runExprs [] env state _ _ = pure (env, state)
runExprs (e : es) env state (IOpts {tc=tc}) b = do
  result <- evalToIO (macroExpand e) env state
  case result of 
    Just (expanded, state') ->
      case toIntermediate expanded env of 
        Right val -> do
          result <- evalToIO (toTIntermediateTop val) env state'
          case result of 
            Just (tint, state'') -> do
              result <- evalToIO (typeCheckTop tint (Ctx.envToCtx env)) env state''
              case result of 
                Just (cint, state''') -> do
                  cint' <- case cint of 
                        Left (t, ty) -> (print ty) >> pure t
                        Right t -> pure t
                  case runExcept (toTopCore cint') of 
                    Right v -> do
                      (fenv, fstate, mval) <- evalTopCore v env state''
                      case mval of 
                        Just v -> print v
                        Nothing -> pure ()
                      pure (fenv, fstate)
                    Left err -> failWith ("toCore err: " <> err)
                Nothing -> pure (env, state)
            Nothing -> pure (env, state)
        Left err -> do
          print err
          pure (env, state)
    Nothing -> do
      print "macro-expansion err"
      pure (env, state)
  where
    failWith err = (putStrLn err) >> (pure (env, state))

evalTopCore :: TopCore -> Environment -> ProgState -> IO (Environment, ProgState, Maybe Normal)   
evalTopCore core env state = do
  out <- evalToIO (evalTop core) env state
  case out of 
    Just (result, state') -> case result of
      Left val -> pure (env, state', Just val)
      Right fnc -> pure (fnc env, state', Nothing)
    Nothing -> pure (env, state, Nothing)
  
