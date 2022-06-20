module Main where

import Control.Monad.Except (runExcept)

import Parse (parseFile, parseRepl)
import Data
import Data.Environments
import Interpret.Eval
import Syntax.Macroexpand 
import Syntax.Intermediate (toIntermediate) 
import Syntax.Conversions (toTIntermediateTop) 
import Typecheck.Typecheck
import qualified Core


import System.IO

import Interpret.Modules (defaultModule)
import qualified Interpret.Context as Ctx
import qualified Data.Map as Map


import Data.Text (pack)
import qualified Data.Map as Map

  -- Parsing Command Line Args
import Options.Applicative
import Data.Semigroup ((<>))

defaultState = ProgState { _uid_counter = 0 }  

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
           dfc <- evalToIO defaultContext (Ctx.empty) defaultState
           case dfc of 
             Just (ctx, state) ->
               if null f then
                 repl ctx state (IOpts {tc=True})
               else  do
                 handle <- openFile f ReadMode
                 contents <- hGetContents handle
                 (ctx', state') <- runInteractively contents ctx state (IOpts {tc=False})
                 repl ctx' state' (IOpts {tc=True})
             Nothing -> 
               putStrLn "error in initialisation"

         -- If we are in compilation mode, then we're expecting  
         else
           putStrLn "compilation not implemented yet!"
  




-- The REPL
  
defaultContext :: EvalM Context 
defaultContext = do
  dfm <- defaultModule
  pure $ ValContext {
  localCtx = Map.empty,
  currentModule = Module dfm,
  globalModule = Module Map.empty }

data IOpts = IOpts { tc :: Bool }
  

repl :: Context -> ProgState -> IOpts -> IO ()
repl ctx state opts = do
  putStr "> "
  hFlush stdout
  lne <- getLine
  case lne of 
    ":q" -> pure ()
    ":t" -> repl ctx state (IOpts {tc = not (tc opts)})
    _ -> do
      case parseRepl "stdin" (pack lne) of
        Left err -> do
          -- print err
          print "parse error"
          repl ctx state opts
        Right val -> do
          (ctx', state') <- runExprs [val] ctx state opts True
          repl ctx' state' opts
          


runInteractively :: String -> Context -> ProgState -> IOpts
                 -> IO (Context, ProgState)
runInteractively str ctx state opts =
  case parseFile "file" (pack str) of
      Left err -> print err >> pure (ctx, state)
      Right vals -> runExprs vals ctx state opts False

-- runExprs takes in an AST list, a context
runExprs :: [AST] -> Context -> ProgState -> IOpts -> Bool
              -> IO (Context, ProgState)
runExprs [] ctx state _ _ = pure (ctx, state)
runExprs (e : es) ctx state (IOpts {tc=tc}) b = do
  result <- evalToIO (macroExpand e) ctx state
  case result of 
    Just (expanded, state') ->
      case toIntermediate expanded ctx of 
        Right val ->
          if tc then do
            -- TODO: eval typechecked 
            tint <- evalToIO (toTIntermediateTop val (toEnv ctx)) ctx state'
            case tint of 
              Just (t, state'') ->
                case runCheckerTop t (toEnv ctx) of    
                  Right res -> do
                    tint <- case res of 
                      Left (tint, ty) -> do
                        print ty
                        pure tint
                      Right tint -> pure tint
                    case runExcept (Core.toTopCore tint) of 
                      Right v -> do
                        (fctx, fstate, mval) <- evalTopCore v ctx state''
                        case mval of 
                          Just v -> print v
                          Nothing -> pure ()
                        pure (fctx, fstate)
                      Left err -> failWith ("toCore err: " <> err)
                  Left err -> failWith err 
              Nothing -> failWith "toTintermediate err "
          else do
            (ctx', state'') <- evalTopList [val] ctx state' b
            runExprs es ctx' state'' (IOpts {tc=tc}) b 
        Left err -> do
          print err
          pure (ctx, state)
    Nothing -> do
      print "macro-expansion err"
      pure (ctx, state)
  where
    failWith err = (putStrLn err) >> (pure (ctx, state))

evalTopCore :: TopCore -> Context -> ProgState -> IO (Context, ProgState, Maybe Expr)   
evalTopCore core ctx state = do
  out <- evalToIO (Core.evalTop core) ctx state
  case out of 
    Just (result, state') -> case result of
      Left val -> pure (ctx, state', Just val)
      Right fnc -> pure (fnc ctx, state', Nothing)
    Nothing -> pure (ctx, state, Nothing)
  

evalTopList :: [Intermediate] -> Context -> ProgState -> Bool
            -> IO (Context, ProgState)
evalTopList [] ctx state _ = pure (ctx, state)
evalTopList (e:es) ctx state b = do
  result <- evalTopLevel e ctx state
  case result of 
    Nothing -> pure (ctx, state)

    -- On a left, some expression was evaluated
    Just (Left val, state') -> 
      if b then do
        print val
        evalTopList es ctx state' b
      else 
        evalTopList es ctx state' b

    -- On a right, some modification was made to the REPL context
    -- this is a /toplevel/ modification, so we do it to the current module,
    -- /not/ the local context! 
    Just (Right bindlist, state') -> do
      let ctx' =
            foldl (\ctx (s, x) -> Ctx.insertCurrent s x ctx) ctx bindlist 
      evalTopList es ctx' state' b

toEnv :: Context -> CheckEnv
toEnv (ValContext {currentModule=curr, globalModule=glbl}) = 
  CheckEnv {tlocalCtx = Map.empty,
            tcurrentModule = curr,
            tglobalModule = glbl}
