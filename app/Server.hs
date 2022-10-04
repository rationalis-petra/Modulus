{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}

module Server where

{- The Server acts as a juiced-up interpreter/REPL, except programs send and
    receive messages, enabling the interpreter to provide linting, hot reload
    and more. -}

import Server.Message

import Data.Text (Text, pack)
import qualified Data.Map as Map
import Control.Concurrent
import Control.Concurrent.STM
import Control.Lens hiding (Context, contains)
import qualified Control.Monad.Except as Except


import Data (EvalM,
             Normal,
             Normal'(NormSct, NormSig),
             CollVal(..),
             TopCore(..),
             Environment,
             Definition,
             ProgState)
import Parse (parseModule)
import Interpret.EvalM (throwError, liftExcept, ask, localF)
import Interpret.Eval (evalToIO, evalToEither, eval, evalDef, loopAction)
import qualified Interpret.Environment as Env
import Syntax.Macroexpand (macroExpand)
import Syntax.Conversions (toIntermediate, toTIntermediateTop, toTopCore)
import Syntax.Utils (getField)
import Typecheck.Typecheck (typeCheckTop)
import Syntax.Utils (typeVal)
import qualified Typecheck.Context as Ctx

  

  

data ModuleHeader = ModuleHeader { _imports :: [String],
                                   _args    :: [String],
                                   _exports :: [String] }

data Module = Module { _vals :: [(String, Normal)],
                       _types :: [(String, Normal)],
                       _header :: ModuleHeader,
                       _sourceCore :: [Definition],
                       _sourceString :: Text  }

data DTree a b = Node (Map.Map a (DTree a b)) (Maybe b)
emptyTree :: DTree a b
emptyTree = Node Map.empty Nothing

type RawTree = DTree String Text
type ModuleTree = DTree String Module




data IState = IState { _progState   :: ProgState,
                       _environment :: Environment,
                       _modules     :: Either RawTree ModuleTree }

$(makeLenses ''IState)
$(makeLenses ''Module)
$(makeLenses ''ModuleHeader)

startServer :: ProgState -> Environment -> IO ()  
startServer dstate denvironment  = do 
  shared <- atomically $ newTQueue 
  forkIO $ server shared
  interpreter (IState dstate denvironment (Right emptyTree)) shared

interpreter :: IState -> TQueue Message -> IO ()
interpreter istate inbox = do
  message <- atomically $ readTQueue inbox
  case message of 
    Kill ->
      putStrLn "exiting..."
    RunMain -> do
      istate' <- runMain istate
      interpreter istate' inbox
    Compile -> do
      let rawTree = (toRaw (istate^.modules))
      let result = compileTree rawTree (istate^.progState) (istate^.environment)
      case result of 
        Right (compiledTree, state') -> do
          let newState = (((set modules (Right compiledTree)) . (set progState  state')) istate) 
          interpreter newState inbox
        Left err -> do
          putStrLn err
          interpreter istate inbox
    UpdateModule path text -> do
      let rawTree = insert path text (toRaw (istate^.modules))
      interpreter (set modules (Left rawTree) istate) inbox
      


runMain :: IState -> IO IState
runMain istate = 
  case view modules istate of 
    Right (Node _ (Just m)) ->
      case getField "main" (m^.vals) of
        Just val -> do
          (out, state') <- loopAction val (istate^.environment) (istate^.progState)
          pure istate
        Nothing -> do
          putStrLn "error: main monad not found"
          pure istate
    Right _ -> do
      putStrLn "error: cannot run main module as it does not exist"
      pure istate
    Left _ -> do
      putStrLn "error: cannot run main it is not compiled"
      pure istate

insert :: Ord a => [a] -> b -> DTree a b -> DTree a b
insert [] val (Node dir maybeVal) = Node dir (Just val) 
insert (s:ss) val (Node dir maybeVal) =
  case Map.lookup s dir of 
    Just subdir -> Node (Map.insert s (insert ss val subdir) dir) maybeVal
    Nothing ->
      Node (Map.insert s (insert ss val emptyTree) (Map.empty)) maybeVal

compileTree :: RawTree -> ProgState -> Environment -> Either String (ModuleTree, ProgState)
compileTree tree state env = evalToEither (my_mnd tree) env state
  where
    my_mnd :: RawTree -> EvalM ModuleTree
    my_mnd (Node dir (Just text)) = do
      dir' <- (let compileSub :: String -> RawTree -> EvalM (Map.Map String ModuleTree) -> EvalM (Map.Map String ModuleTree)
                   compileSub key val dir' = do
                                  dir'' <- dir'
                                  val' <- my_mnd val
                                  pure $ Map.insert key val' dir''
                in Map.foldrWithKey compileSub (pure Map.empty) dir)

      
      ((inp, exp, _), terms) <- case parseModule "main" text of 
        Right val -> pure val 
        Left err -> throwError (show err)

      -- resolve imports statements
      imports <- liftExcept $ resolveImports inp dir'
      localF (flip (foldr (\(k, v) env -> Env.insert k v env)) imports) $ do

        let foldTerms [] = pure ([], [], [])
            foldTerms (def:defs) = do
              expanded <- macroExpand def
              env <- ask
              let eintermediate = toIntermediate expanded env  
              intermediate <- (case eintermediate of Right val -> pure val; Left err -> throwError err)
              tintermediate <- toTIntermediateTop intermediate
              env <- ask
              checked <- typeCheckTop tintermediate (Ctx.envToCtx env)

              -- TODO: integrate type-checking results into allTypes
              let justvals = (case checked of Left (val, _) -> val; Right val -> val)
              core <- liftExcept (toTopCore justvals)
              def <- liftExcept (getAsDef core)
              vals <- evalDef def
              allTypes <- liftExcept (mapM (\(k, v) -> ((,) k) <$> typeVal v) vals)
              (defs, vals', allTypes') <- localF (flip (foldr (\(k, v) -> Env.insert k v)) vals) (foldTerms defs)
              pure (def : defs, vals <> vals', allTypes <> allTypes')

        -- can carry forward for typechecking etc.
        (defs, vals, allTypes) <- foldTerms terms
        -- restrict the types to be only our exports!
        let types = foldr (\(k, v) rest -> if contains k exp then ((k, v) : rest) else rest) [] allTypes
        
       
        pure (Node dir' (Just $ Module {
                               _vals=vals,
                               _types=types,
                               _header=ModuleHeader [] [] [],
                               _sourceCore=defs,
                               _sourceString=text}))

    my_mnd _ = throwError "no main module" 

resolveImports :: [String] -> Map.Map String ModuleTree -> Except.Except String [(String, Normal)]
resolveImports [] _ = pure []
resolveImports (s:ss) dict = 
  case Map.lookup s dict of  
    Just (Node _ ( Just (Module {_vals=vals, _types=types}))) -> do
      tl <- resolveImports ss dict
      pure $ (s, NormSct vals (NormSig types)) : tl
    _ -> Except.throwError ("couldn't find import: " <> s)
  
        
       
toRaw :: (Either RawTree ModuleTree ) -> RawTree
toRaw (Right v) = toRaw' v 
  where
    toRaw' (Node dir (Just (Module {_sourceString=str}))) =
      Node (Map.map toRaw' dir) (Just str)
    toRaw' (Node dir Nothing) = 
      Node (Map.map toRaw' dir) Nothing 
toRaw (Left raw) = raw


      
getAsDef :: TopCore  -> Except.Except String Definition
getAsDef (TopDef definition) = pure definition
getAsDef _ = Except.throwError "not definition"






-- Server/IO Section  
server :: TQueue Message -> IO ()
server outbox = do
  atomically $ writeTQueue outbox $ UpdateModule ["lib"] (pack "(module lib (export dostuff)) (def mystring \"hello, world!\") (def dostuff (sys.put_line mystring))")
  atomically $ writeTQueue outbox $ UpdateModule [] (pack "(module main (import lib)) (def main lib.dostuff)")
  atomically $ writeTQueue outbox Compile
  atomically $ writeTQueue outbox RunMain
  atomically $ writeTQueue outbox Kill
  pure ()


  
contains _ [] = False 
contains x (y:ys) | x == y = True
contains x (_:ys) = contains x ys
