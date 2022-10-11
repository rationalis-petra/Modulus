module Server.Interpret (interpreter) where

import Control.Concurrent
import Control.Concurrent.STM

import qualified Data.Map as Map 
import qualified Interpret.Environment as Env
import Control.Lens hiding (Context, contains)
import qualified Control.Monad.Except as Except

import Parse (parseModule)
import Interpret.Eval (evalToIO, evalToEither, eval, evalDef, loopAction)
import Interpret.EvalM (throwError, liftExcept, ask, localF)
import Syntax.Macroexpand (macroExpand)
import Syntax.Conversions (toIntermediate, toTIntermediateTop, toTopCore)
import Typecheck.Typecheck (typeCheckTop)
import Syntax.Utils (typeVal)

import Syntax.Utils (getField)
import Data(Normal,
            Normal'(NormSct, NormSig),
            ProgState,
            TopCore(..),
            Environment,
            Definition,
            EvalM,
            toEmpty)

import Server.Data
import Server.Message
import Server.Parse


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
      let rawTree = toRaw (istate^.modules)
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

compileTree :: RawTree -> ProgState -> Environment -> Either String (ModuleTree, ProgState)
compileTree tree state ctx = evalToEither (my_mnd tree) ctx state
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
      localF (flip (foldr (\(k, (v, ty)) -> Env.insert k v ty)) imports) $ do

        let foldTerms [] = pure ([], [])
            foldTerms (def:defs) = do
              expanded <- macroExpand def
              env <- ask
              let eintermediate = toIntermediate expanded env  
              intermediate <- (case eintermediate of Right val -> pure val; Left err -> throwError err)
              tintermediate <- toTIntermediateTop intermediate
              env <- ask
              checked <- typeCheckTop tintermediate env

              -- TODO: integrate type-checking results into allTypes
              let justvals = (case checked of Left (val, _) -> val; Right val -> val)
              core <- liftExcept (toTopCore justvals)
              def <- liftExcept (getAsDef core)
              vals <- evalDef def
              (defs, vals') <- localF (flip (foldr (\(k, (v, ty)) -> Env.insert k v ty)) vals) (foldTerms defs)
              pure (def : defs, vals <> vals')

        -- can carry forward for typechecking etc.
        (defs, vals) <- foldTerms terms
        let (vals', allTypes) = foldr (\(k, (v, ty)) (vals, types) -> (((k, v) : vals), ((k, ty) : types))) ([], []) vals
        -- restrict the types to be only our exports!
        let types = foldr (\(k, v) rest -> if contains k exp then ((k, v) : rest) else rest) [] allTypes
       
        pure (Node dir' (Just $ Module {
                               _vals=vals',
                               _types=types,
                               _header=ModuleHeader [] [] [],
                               _sourceCore=defs,
                               _sourceString=text}))

    my_mnd _ = throwError "no main module" 

resolveImports :: [String] -> Map.Map String ModuleTree -> Except.Except String [(String, (Normal, Normal))]
resolveImports [] _ = pure []
resolveImports (s:ss) dict = 
  case Map.lookup s dict of  
    Just (Node _ ( Just (Module {_vals=vals, _types=types}))) -> do
      tl <- resolveImports ss dict
      pure $ (s, (NormSct (toEmpty vals) (NormSig types), (NormSig types))) : tl
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
