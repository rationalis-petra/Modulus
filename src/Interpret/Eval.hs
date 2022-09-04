module Interpret.Eval (Normal,
                       EvalM,
                       evalToIO,
                       eval,
                       evalTop,
                       normSubst,

                       liftFun,
                       liftFun2,
                       liftFun3,
                       liftFun4) where

import Prelude hiding (lookup)

import Control.Monad.State (State, runState)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.Reader (ReaderT, runReaderT)
import qualified Interpret.Environment as Env

import Syntax.Utils  
import Interpret.EvalM
  
import Data
import qualified Data.Map as Map
import qualified Data.Set as Set
import Interpret.Transform hiding (lift)


evalTop :: TopCore -> EvalM (Either Normal (Environment -> Environment))
evalTop (TopExpr e) = eval e >>= (\val -> pure (Left val))
evalTop (TopDef def) = case def of
  SingleDef name body ty -> do
    val <- eval body
    pure (Right (Env.insertCurrent name val))
  OpenDef body sig -> do
    mdle <- eval body
    case mdle of 
      NormMod m -> do
        let m' = restrict m sig 
        pure (Right (\env -> foldr (\(k, val) env -> Env.insertCurrent k val env) env m'))
      _ -> throwError "cannot open non-module"
  InductDef sym indid params ty alts -> do 
    let insertCtor env = Env.insertCurrent sym ty env
        insertAlts alts env = foldr (\(k, val) env -> Env.insertCurrent k val env) env alts

        mkAlts [] = pure []
        mkAlts ((sym, id, ty) : alts) = do
          alt <- mkAlt sym id ty []
          alts' <- mkAlts alts
          pure ((sym, alt) : alts')
          
        mkAlt :: String -> Int -> Normal -> [Normal] -> EvalM Normal
        mkAlt sym id (NormArr l r) params = do
          var <- fresh_var 
          subterm <- mkAlt sym id r ((Neu $ NeuVar ("#" <> show var)): params)
          pure $ NormAbs ("#" <> show var) subterm (NormArr l r)
        mkAlt sym id (NormProd var a b) params = do
          subterm <- mkAlt sym id b (Neu (NeuVar var) : params)
          pure $ NormAbs var subterm (NormProd var a b)
        mkAlt sym id (NormImplProd var a b) params = do
          subterm <- mkAlt sym id b (Neu (NeuVar var) : params)
          pure $ NormAbs var subterm (NormImplProd var a b)
        mkAlt sym id ty params = pure $ NormIVal sym indid id (reverse params) ty
    
    alts' <- mkAlts alts
    pure $ Right (insertCtor . insertAlts alts')
  
-- evaluate an expression, to a normal form (not a value!). This means that the
-- environment now contains only normal forms!
eval :: Core -> EvalM Normal
eval (CNorm n) = pure n
eval (CVar var) = do
  env <- ask
  case Env.lookup var env of 
    Just val -> pure val
    Nothing -> throwError ("could not find variable " <> var <> " in context")

eval (CArr l r) = do
  l' <- eval l 
  r' <- eval r
  pure $ NormArr l' r'
  
eval (CProd var a b) = do
  a' <- eval a
  b' <- localF (Env.insert var (Neu (NeuVar var))) (eval b)
  pure $ NormProd var a' b'

eval (CImplProd var a b) = do
  a' <- eval a
  b' <- localF (Env.insert var (Neu (NeuVar var))) (eval b)
  pure $ NormImplProd var a' b'

eval (CAbs var body ty) = do   
  body' <- localF (Env.insert var (Neu (NeuVar var))) (eval body)
  pure $ NormAbs var body' ty

eval (CApp l r) = do
  l' <- eval l
  r' <- eval r
  case l' of 
    Neu neu -> pure $ Neu (NeuApp neu r')
    NormAbs var body ty -> do
      -- if t_hasType r' ty then
      normSubst (r', var) body
      -- else
      --   throwError "bad type application"
    Builtin fn ty -> fn r'

eval (CSct defs) = do
  defs' <- foldDefs defs
  pure $ NormMod $ defs'
  where
    foldDefs :: [Definition] -> EvalM  [(String, Normal)]
    foldDefs [] = pure []
    foldDefs (def : defs) = do
      case def of  
        SingleDef var core ty -> do
          val <- eval core
          defs' <- localF (Env.insert var val) (foldDefs defs)
          pure ((var, val) : defs')

eval (CSig defs) = do
  defs' <- foldDefs defs
  pure $ NormSig $ defs'
  where
    foldDefs :: [Definition] -> EvalM  [(String, Normal)]
    foldDefs [] = pure []
    foldDefs (def : defs) = do
      case def of
        SingleDef var core ty -> do
          val <- eval core
          defs' <- localF (Env.insert var val) (foldDefs defs)
          pure ((var, val) : defs')

eval (CDot ty field) = do
  ty' <- eval ty
  case ty' of 
    Neu neu ->
      pure $ Neu (NeuDot neu field)
    NormSig fields -> case getField field fields of
      Just val -> pure val
      Nothing -> throwError ("can't find field" <> field)
    NormMod fields -> case getField field fields of 
      Just val -> pure val
      Nothing -> throwError ("can't find field" <> field)
    non -> throwError ("value does is not structure" <> show non)


normSubst :: (Normal, String) -> Normal -> EvalM Normal
normSubst (val, var) ty = case ty of 
  Neu neu -> neuSubst (val, var) neu
  PrimType p -> pure $ PrimType p
  PrimVal p -> pure $ PrimVal p
  NormUniv n -> pure $ NormUniv n

  
  NormProd var' a b ->
    if var == var' then  do
      a' <- normSubst (val, var) a
      pure $ NormProd var' a' b
    else do
      a' <- normSubst (val, var) a
      b' <- normSubst (val, var) b
      pure $ NormProd var' a' b'
  NormImplProd var' a b -> 
    if var == var' then  do
      a' <- normSubst (val, var) a
      pure $ NormImplProd var' a' b
    else do
      a' <- normSubst (val, var) a
      b' <- normSubst (val, var) b
      pure $ NormImplProd var' a' b'
  NormArr a b -> do
      a' <- normSubst (val, var) a
      b' <- normSubst (val, var) b
      pure $ NormArr a' b'
  NormAbs var' body ty -> do 
    if var == var' then  do
      ty' <- normSubst (val, var) ty
      pure $ NormAbs var' body ty'
    else do
      body' <- normSubst (val, var) body
      ty' <- normSubst (val, var) ty
      pure $ NormAbs var' body' ty'


  NormMod fields -> do
    NormMod <$> substFields (val, var) fields
  NormSig fields -> do
    NormSig <$> substFields (val, var) fields

  -- IOAction

  BuiltinMac m -> pure $ BuiltinMac m
  Special sp   -> pure $ Special sp
  Keyword key  -> pure $ Keyword key
  Symbol sym   -> pure $ Symbol sym
  AST ast      -> pure $ AST ast

  -- Undef 
  s -> throwError ("subst not implemented for: " <> show s)
  where 
    substFields :: (Normal, String) -> [(String, Normal)] -> EvalM [(String, Normal)]
    substFields (val, var) ((var', val') : fields) = do
      if var == var' then 
        pure $ (var', val') : fields
      else do
        val'' <- normSubst (val, var) val'
        fields' <- substFields (val, var) fields 
        pure $ (var', val'') : fields'
    substFields (val, var) [] = pure []

  
neuSubst :: (Normal, String) -> Neutral -> EvalM Normal
neuSubst (val, var) neutral = case neutral of 
  NeuVar var' ->
    if var == var' then
      pure val
    else 
      pure $ Neu (NeuVar var')
  NeuApp l r -> do
    l' <- neuSubst (val, var) l
    r' <- normSubst (val, var) r
    case l' of 
      Neu n -> pure $ Neu (NeuApp n r')
      NormProd var a b -> do
        if t_hasType r' a then
          normSubst (r', var) b
        else
          throwError "bad type application"
      Builtin fn ty -> fn r'
      v -> throwError ("bad app:" <> show v)

  NeuBuiltinApp fn neu ty -> do
    arg <- neuSubst (val, var) neu
    fn arg
      
  NeuBuiltinApp2 fn neu ty -> do
    arg <- neuSubst (val, var) neu
    pure (liftFun (fn arg) ty)

  NeuBuiltinApp3 fn neu ty -> do
    arg <- neuSubst (val, var) neu
    pure (liftFun2 (fn arg) ty)

  -- NeuDot sig field -> do
  --   sig' <- neuSubst 



instance Eq (Normal' m) where
  a == b = norm_equiv a b (Set.empty, 0) (Map.empty, Map.empty)


-- TODO: add η reductions to the equality check
norm_equiv :: (Normal' m) -> (Normal' m) -> Generator -> (Map.Map String String, Map.Map String String) -> Bool 
norm_equiv (NormUniv n1) (NormUniv n2) gen rename = n1 == n2
norm_equiv (Neu n1) (Neu n2) gen rename = neu_equiv n1 n2 gen rename
norm_equiv (PrimVal p1) (PrimVal p2) _ _ = p1 == p2
norm_equiv (PrimType p1) (PrimType p2) _ _ = p1 == p2

-- Note: arrows and dependent types /can/ be equivalent if the bound variable
-- doesn't come on the LHS
norm_equiv (NormProd var a b) (NormProd var' a' b') gen (lrename, rrename) = 
  let (nvar, gen') = genFresh gen
  in (a == a') && (norm_equiv b b'
                   (useVars [var, var', nvar] gen')
                   (Map.insert var nvar lrename, Map.insert var' nvar rrename))
norm_equiv (NormArr a b)     (NormArr a' b') gen rename = 
  (norm_equiv a a' gen rename) || (norm_equiv b b' gen rename)
norm_equiv (NormProd var a b) (NormArr a' b') gen rename = 
  if Set.member var (free b) then
    False
  else
    norm_equiv a a' gen rename && norm_equiv b b' gen rename
norm_equiv (NormArr  a b) (NormProd var' a' b') gen rename = 
  if Set.member var' (free b') then
    False
  else
    norm_equiv a a' gen rename && norm_equiv b b' gen rename
-- norm_equiv (NormImplProd var a b) (NormImplProd var' a' b') gen rename = 
--   (var a b) || ()



  
neu_equiv :: (Neutral' m) -> (Neutral' m) -> Generator -> (Map.Map String String, Map.Map String String)
        -> Bool 
neu_equiv (NeuVar v1) (NeuVar v2) used (lrename, rrename) =
  case (Map.lookup v1 lrename, Map.lookup v2 rrename) of
    (Just v1', Just v2') -> v1 == v2
    (_, _) -> False
neu_equiv (NeuApp l1 r1) (NeuApp l2 r2) used rename = 
  (neu_equiv l1 l2 used rename) && (norm_equiv r1 r2 used rename)
neu_equiv (NeuDot neu1 field1) (NeuDot neu2 field2) used rename
  = (field1 == field2) && neu_equiv neu1 neu2 used rename 





type Generator = (Set.Set String, Int)  

useVar :: String -> Generator -> Generator  
useVar var (set, id) = (Set.insert var set, id)

useVars :: [String] -> Generator -> Generator  
useVars vars (set, id) = (foldr Set.insert set vars, id)

  
genFresh :: Generator -> (String, Generator)
genFresh (set, id) =
  let var = ("#" <> show id)
  in
    if Set.member var set then
      genFresh (set, id+1)
    else
      (var, (Set.insert var set, id+1))


evalToIO :: EvalM a -> Environment -> ProgState -> IO (Maybe (a, ProgState))
evalToIO (ActionMonadT inner_mnd) ctx state =
  case runState (runExceptT (runReaderT inner_mnd ctx)) state of
    (Right (Value obj), state') -> do
      return $ Just (obj, state')
    (Right (RaiseAction cnt id1 id2 args (Just f)), state') -> do
      result <- f args
      accumEffects result cnt state'
    (Right (RaiseAction cnt id1 id2 args Nothing), state') -> do
      putStrLn $ "Action Called Without Being Handled: ("  ++ show id2 ++ "," ++ show id2 ++ ")"
      return Nothing
    (Left err, state') -> do
      putStrLn $ "error: " ++ err
      return Nothing
  where
    accumEffects :: EvalM Normal -> (Normal -> EvalM a) -> ProgState -> IO (Maybe (a, ProgState))
    accumEffects (ActionMonadT inner_mnd) cnt state = 
      case runState (runExceptT (runReaderT inner_mnd ctx)) state of
        (Right (RaiseAction cnt2 id1 id2 args (Just f)), state') -> do 
          result <- f args
          accumEffects result (\x -> cnt2 x >>= cnt) state'
        (Right (Value obj), state') -> do
          evalToIO (cnt obj) ctx state'
        (Right (RaiseAction _ id1 id2 _ Nothing), state') -> do
          putStrLn $ "Action Called Without Default" ++ show (id1, id2)
          return Nothing
        (Left err, state') -> do
          putStrLn $ "error: " ++ err
          return Nothing


interceptNeutral :: (Normal -> EvalM Normal) -> Normal -> Normal -> EvalM Normal
interceptNeutral f ty (Neu neutral) = pure $ Neu (NeuBuiltinApp (interceptNeutral f ty) neutral ty)
interceptNeutral f ty val = f val


-- liftFun needs to intercept /neutral/ terms!
liftFun :: (Normal -> EvalM Normal) -> Normal -> Normal
liftFun f ty = Builtin (interceptNeutral f ty) ty

liftFun2 :: (Normal -> Normal -> EvalM Normal) -> Normal -> Normal
liftFun2 f ty =
  let f' = f in
    Builtin (\val -> case val of
                (Neu neu) -> pure $ Neu $ NeuBuiltinApp2 f neu ty
                _ ->
                  case ty of
                    (NormArr _ r) -> pure $ liftFun (f' val) r
                    (NormProd var _ body) -> pure $ liftFun (f' val) body
                    (NormImplProd var _ body) -> pure $ liftFun (f' val) body)
    ty

liftFun3 :: (Normal -> Normal -> Normal -> EvalM Normal) -> Normal -> Normal 
liftFun3 f ty =
  let f' = f in
    Builtin (\val -> case val of
                (Neu neu) -> pure $ Neu $ NeuBuiltinApp3 f neu ty
                _ -> case ty of
                  (NormArr _ r) -> pure $ liftFun2 (f' val) r
                  (NormProd var _ body) -> pure $ liftFun2 (f' val) body
                  (NormImplProd var _ body) -> do pure $ liftFun2 (f' val) body)
    ty

liftFun4 :: (Normal -> Normal -> Normal -> Normal -> EvalM Normal) -> Normal -> Normal 
liftFun4 f ty =
  let f' = f in
    Builtin (\val -> case val of
                (Neu neu) -> pure $ Neu $ NeuBuiltinApp4 f neu ty
                _ -> case ty of
                  (NormArr _ r) -> pure $ liftFun3 (f val) r
                  (NormProd var _ body) -> pure $ liftFun3 (f val) body
                  (NormImplProd var _ body) -> pure $ liftFun3 (f val) body)
    ty

