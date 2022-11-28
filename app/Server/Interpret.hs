{-# LANGUAGE FlexibleContexts #-}
module Server.Interpret (interpreter) where

import Control.Concurrent
import Control.Concurrent.STM

import qualified Data.Map as Map 
import qualified Interpret.Environment as Env
import Control.Lens hiding (Context, contains)
import Control.Monad.State (State, MonadState)
import Control.Monad.Except (ExceptT, MonadError, throwError)
import Control.Monad.Reader (ReaderT, MonadReader, local, ask)

import Bindings.Libtdl  

import Syntax.Normal(Normal(NormSct, NormSig, NormCModule, PrimType),
                     PrimType(CModuleT),
                     ProgState,
                     Environment,
                     AST,
                     toEmpty)
import Syntax.Core(Core, TopCore(..), Definition)
import Parse (parseModule)
import Interpret.Eval (eval, evalDef, runIO)
import Interpret.EvalM (runEval, Eval)
import Syntax.Utils (typeVal, getField)
import Syntax.Macroexpand (macroExpand)
import Syntax.Conversions (toIntermediate, toTIntermediateTop, toTopCore)
import Typecheck.Typecheck (typeCheckTop, annotate)

import Server.Data
import Server.Message


interpreter :: IState Eval -> TQueue Message -> IO ()
interpreter istate inbox = do
  message <- atomically $ readTQueue inbox
  case message of 
    Kill ->
      putStrLn "exiting..."
    RunMain -> do
      istate' <- runMain istate
      interpreter istate' inbox
    Compile -> do
      let rawTree = toRaw (istate^.modules)
      result <- compileTree rawTree (istate^.progState) (istate^.environment)
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


runMain :: IState Eval -> IO (IState Eval)
runMain istate = 
  case view modules istate of 
    Right (Node _ (Just m)) ->
      case getField "main" (m^.vals) of
        Just val -> do
          (out, state') <- runIO val (istate^.environment) (istate^.progState)
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


compileTree :: RawTree -> ProgState Eval -> Environment Eval -> IO (Either String (ModuleTree Eval, ProgState Eval))
compileTree (Node dir mtext) state ctx = do
  case mtext of 
    Just text -> do 
      res <- recurse dir
      case res of 
        Right (dir', state') -> 
          case parseModule "main" text of
            Right ((inp, fmdles, exp, _), terms) -> do
              mfmodules  <- resolveForeign fmdles
              case mfmodules of 
                Just fModules -> pure $ runEval ((Node dir' . Just) <$> compileModule ((inp, fModules, exp), terms) text dir') ctx state' 
                Nothing -> pure $ Left ("failed to load foreign modules " <> show fmdles)
            Left err -> pure $ Left $ show err
        Left err -> pure $ Left err
    Nothing -> do
      res <- recurse dir
      case res of 
        Right (val, state) -> pure $ Right (Node val Nothing, state)
        Left err -> pure $ Left err
  where

    recurse dir = do
      let compileSub :: String -> RawTree -> IO (Either String (Map.Map String (ModuleTree Eval), ProgState Eval)) -> IO (Either String (Map.Map String (ModuleTree Eval), ProgState Eval))
          compileSub key val mnd = do
            res <- mnd
            case res of 
              Right (dir', state) -> do
                res <- compileTree val state ctx
                case res of 
                  Right (val', state') -> pure $ Right $ (Map.insert key val' dir', state')
                  Left err -> pure $ Left err
              Left err -> pure $ Left err 
       in Map.foldrWithKey compileSub (pure $ Right (Map.empty, state)) dir

      
    compileModule ((inp, fmdles, exp), terms) source dir = do
      imports <- resolveImports inp dir
      let addToEnv = flip (foldr (\(k, (v, ty)) -> Env.insert k v ty))
      local (addToEnv imports . addToEnv fmdles) $ do

        let foldTerms ty [] = pure ([], [])
            foldTerms ty (def:defs) = do
              expanded <- macroExpand def
              env <- ask
              let eintermediate = toIntermediate expanded env  
              intermediate <- (case eintermediate of Right val -> pure val; Left err -> throwError err)
              tintermediate <- toTIntermediateTop intermediate
              env <- ask
              -- TODO: typechecking should be monadic
              checked <- case ty of 
                Just ty -> do
                  annotated <- annotate tintermediate ty
                  typeCheckTop annotated env
                Nothing -> typeCheckTop tintermediate env

              -- TODO: integrate type-checking results into allTypes
              let justvals = (case checked of Left (val, _) -> val; Right val -> val)
              core <- toTopCore justvals

              res <- defOrAnn core
              case res of 
                Left def -> do
                  -- TODO: if vals is a type-annotation, we must here
                  vals <- evalDef def
                  (defs, vals') <- local (flip (foldr (\(k, (v, ty)) -> Env.insert k v ty)) vals) (foldTerms Nothing defs)
                  pure (def : defs, vals <> vals')
                Right (str, core) -> do
                  ty <- eval core
                  foldTerms (Just ty) defs


        -- can carry forward for typechecking etc.
        (defs, vals) <- foldTerms Nothing terms
        let (vals', allTypes) = foldr (\(k, (v, ty)) (vals, types) -> (((k, v) : vals), ((k, ty) : types))) ([], []) vals
        -- restrict the types to be only our exports!
        let types = foldr (\(k, v) rest -> if contains k exp then ((k, v) : rest) else rest) [] allTypes
       
        pure (Module
              { _vals=vals'
              , _types=types
              , _header=ModuleHeader [] [] []
              , _sourceCore=defs
              , _sourceString=source
              })
  

resolveImports :: MonadError String m => [String] -> Map.Map String (ModuleTree m) -> m [(String, (Normal m, Normal m))]
resolveImports [] _ = pure []
resolveImports (s:ss) dict = 
  case Map.lookup s dict of  
    Just (Node _ ( Just (Module {_vals=vals, _types=types}))) -> do
      tl <- resolveImports ss dict
      pure $ (s, (NormSct (toEmpty vals) (NormSig types), (NormSig types))) : tl
    _ -> throwError ("couldn't find import: " <> s)

  
resolveForeign :: [(String, String)] -> IO (Maybe [(String, (Normal m, Normal m))])
resolveForeign vals = do
  maybes <- mapM loadModule (map snd vals)
  pure $ zip (map fst vals) <$> mapM (fmap $ flip (,) (PrimType CModuleT) . NormCModule) maybes
        
       
toRaw :: (Either RawTree (ModuleTree m)) -> RawTree
toRaw (Right v) = toRaw' v 
  where
    toRaw' (Node dir (Just (Module {_sourceString=str}))) =
      Node (Map.map toRaw' dir) (Just str)
    toRaw' (Node dir Nothing) = 
      Node (Map.map toRaw' dir) Nothing 
toRaw (Left raw) = raw

      
defOrAnn :: MonadError String m => TopCore m -> m (Either (Definition m) (String, Core m))
defOrAnn (TopDef definition) = pure $ Left definition
defOrAnn (TopAnn str core) = pure $ Right (str, core) 
defOrAnn (TopExpr _) = throwError "toplevel expression encountered"

  
contains _ [] = False 
contains x (y:ys) | x == y = True
contains x (_:ys) = contains x ys


insert :: Ord a => [a] -> b -> DTree a b -> DTree a b
insert [] val (Node dir maybeVal) = Node dir (Just val) 
insert (s:ss) val (Node dir maybeVal) =
  case Map.lookup s dir of 
    Just subdir -> Node (Map.insert s (insert ss val subdir) dir) maybeVal
    Nothing ->
      Node (Map.insert s (insert ss val emptyTree) (Map.empty)) maybeVal

