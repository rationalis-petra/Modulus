{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}

module Server where

{- The Server acts as a juiced-up interpreter/REPL, except programs send and
    receive messages, enabling the interpreter to provide linting, hot reload
    and more. -}

import Data.Text (Text, pack)
import qualified Data.Map as Map
import Control.Concurrent
import Control.Concurrent.STM
import Control.Lens hiding (Context)
import qualified Control.Monad.Except as Except


import Data (EvalM, Normal, CollVal(..), TopCore(..), Environment, Definition, ProgState)
import Parse (parseModule)
import Interpret.EvalM (throwError, liftExcept, ask)
import Interpret.Eval (evalToIO, evalToEither, eval, evalDef, loopAction)
import Syntax.Macroexpand (macroExpand)
import Syntax.Conversions (toIntermediate, toTIntermediateTop, toTopCore)
import Syntax.Utils (getField)
import Typecheck.Typecheck (typeCheckTop)
import qualified Typecheck.Context as Ctx

  

  

data ModuleHeader = ModuleHeader { _imports :: [String],
                                   _args    :: [String],
                                   _exports :: [String] }

data Module = Module { _vals :: [(String, Normal)],
                       _header :: ModuleHeader,
                       _sourceCore :: [Definition],
                       _sourceString :: Text  }

data DTree a b
  = Node (Map.Map a (DTree a b)) (Maybe b)
emptyTree :: DTree a b
emptyTree = Node Map.empty Nothing

type RawTree = DTree String Text
type ModuleTree = DTree String Module



data Message
  = UpdateModule [String] Text
  | RunMain
  | Kill

data IState = IState { _progState   :: ProgState,
                       _environment :: Environment,
                       _moduleTree  :: ModuleTree }

$(makeLenses ''IState)
$(makeLenses ''Module)
$(makeLenses ''ModuleHeader)

startServer :: ProgState -> Environment -> IO ()  
startServer dstate denvironment  = do 
  shared <- atomically $ newTQueue 
  forkIO $ interpreter (IState dstate denvironment emptyTree) shared
  forkIO $ server shared
  threadDelay 2000000

interpreter :: IState -> TQueue Message -> IO ()
interpreter istate inbox = do
  message <- atomically $ readTQueue inbox
  case message of 
    Kill -> putStrLn "exiting..."
    RunMain -> do
      istate' <- runMain istate
      interpreter istate' inbox
    UpdateModule path text -> do
      let rawTree = insert path text (toRaw (istate^.moduleTree))
      let result = compileTree rawTree (istate^.progState) (istate^.environment)
      case result of 
        Right (compiledTree, state') -> do
          let newState = (((set moduleTree compiledTree) . (set progState  state')) istate) 
          interpreter newState inbox
        Left err -> do
          putStrLn err
          interpreter istate inbox
      

server :: TQueue Message -> IO ()
server outbox = do
  atomically $ writeTQueue outbox $ UpdateModule [] (pack "(module) (def main (sys.put_line \"hello, world!\"))")
  atomically $ writeTQueue outbox RunMain
  atomically $ writeTQueue outbox Kill
  pure ()

runMain :: IState -> IO IState
runMain istate = do
  let Node _ mdle = view moduleTree istate
  case mdle of 
    Just m -> 
      case getField "main" (m^.vals) of
        Just val -> do
          (out, state') <- loopAction val (istate^.environment) (istate^.progState)
          pure istate
        Nothing -> do
          putStrLn "error: main monad not found"
          pure istate
    Nothing -> do
      putStrLn "error: cannot run main module as it does not exist"
      pure istate

insert :: Ord a => [a] -> b -> DTree a b -> DTree a b
insert [] val (Node dir maybeVal) = Node dir (Just val) 
insert (s:ss) val (Node dir maybeVal) =
  case Map.lookup s dir of 
    Just subdir -> Node (Map.insert s (insert ss val subdir) dir) maybeVal
    Nothing ->
      Node (Map.insert s (insert ss val emptyTree) (Map.empty)) maybeVal

compileTree :: RawTree -> ProgState -> Environment -> Either String (ModuleTree, ProgState)
compileTree (Node _ (Just text)) state env = evalToEither my_mnd env state
  where
    my_mnd :: EvalM ModuleTree
    my_mnd = do
      (header, defs) <- case parseModule "main" text of 
        Right val -> pure val 
        Left err -> throwError (show err)
      -- TOOD: replace uses of mapM with a fold so, e.g. macros and definitions
      -- can carry forward for typechecking etc.
      expanded <- mapM macroExpand defs
      env <- ask
      let eintermediate = map (flip toIntermediate env) expanded 
      intermediate <- mapM (\case Right val -> pure val; Left err -> throwError err) eintermediate
      tintermediate <- mapM toTIntermediateTop intermediate
      env <- ask
      checked <- mapM (flip typeCheckTop (Ctx.envToCtx env)) tintermediate 
      let justvals = map (\case Left (val, _) -> val; Right val -> val) checked
      core <- liftExcept (mapM toTopCore justvals)
      defs <- liftExcept (mapM getAsDef core)
      vals <- (mapM evalDef defs)
      pure (Node Map.empty (Just
                            Module {
                             _vals=(flatten vals),
                             _header=ModuleHeader [] [] [],
                             _sourceCore=defs,
                             _sourceString=text}))
compileTree _ _ _ = Left "no main module" 
        
       
toRaw :: ModuleTree -> RawTree
toRaw (Node dir (Just (Module {_sourceString=str}))) = 
  Node (Map.map toRaw dir) (Just str) 
toRaw (Node dir Nothing) = 
  Node (Map.map toRaw dir) Nothing 

      
getAsDef :: TopCore  -> Except.Except String Definition
getAsDef (TopDef definition) = pure definition
getAsDef _ = Except.throwError "not definition"


flatten :: [[a]] -> [a]
flatten = (foldr (<>)) []
