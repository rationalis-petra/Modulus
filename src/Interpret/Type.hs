module Interpret.Type where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data (TypeExpr(..),
             TypeNormal(..),
             TypeNeutral(..),
             Value(Type),
             Environment,
             EvalM) 
import Interpret.EvalM
import Typecheck.TypeUtils
import qualified Interpret.Environment as Env

insertType :: String -> TypeNormal -> Environment -> Environment
insertType var = (Env.insert var) . Type
  
  
-- evaluate an expression, to a normal form (not a value!). This means that the
-- environment now contains only normal forms!
eval :: TypeExpr -> EvalM TypeNormal
eval (TyNorm n) = pure n
eval (TyVar var) = do
  env <- ask
  case Env.lookup var env of 
    Just (Type ty) -> pure ty
    Just other -> throwError ("value is not a type: " <> show other)
    Nothing -> throwError ("could not find type variable" <> var <> " in context")

eval (TyArr l r) = do
  l' <- eval l 
  r' <- eval r
  pure $ NormArr l' r'
  
eval (TyDep var a b) = do
  a' <- eval a
  b' <- localF (insertType var a') (eval b)
  pure $ NormDep var a' b'

eval (TyImplDep var a b) = do
  a' <- eval a
  b' <- localF (insertType var (Neu (NeuVar var))) (eval b)
  pure $ NormImplDep var a' b'

eval (TyApp l r) = do
  l' <- eval l
  r' <- eval r
  case l' of 
    Neu neu -> pure $ Neu (NeuApp neu r')
    NormArr _ r -> pure r 
    NormDep var ty body -> do
      if t_hasType r' ty then
        normSubst (r', var) body
      else
        throwError "bad type application"

-- eval (TySig defs) = do
--   NormSig $ foldDefs defs
--   where
--     foldDefs :: [(String, TypeExpr)] -> EvalM  [(String, TypeNormal)]
--     foldDefs [] = pure []
--     foldDefs ((var, ty) : defs) = do
--       ty' <- eval ty
--       localF (insertType var ty') (eval $ foldDefs defs)

eval (TyDot ty field) = do
  ty' <- eval ty
  case ty' of 
    Neu neu ->
      pure $ Neu (NeuDot neu field)
    NormSig sig -> case getField field sig of
      Just val -> pure val
      Nothing -> throwError ("can't find field" <> field)


normSubst :: (TypeNormal, String) -> TypeNormal -> EvalM TypeNormal
normSubst (val, var) ty = case ty of 
  Neu neu -> neuSubst (val, var) neu
  NormPrim p -> pure $ NormPrim p
  NormUniv n -> pure $ NormUniv n
  NormDep var' a b ->
    if var == var' then  do
      a' <- normSubst (val, var) a
      pure $ NormDep var' a' b
    else do
      a' <- normSubst (val, var) a
      b' <- normSubst (val, var) b
      pure $ NormDep var' a' b'
  NormImplDep var' a b -> 
    if var == var' then  do
      a' <- normSubst (val, var) a
      pure $ NormImplDep var' a' b
    else do
      a' <- normSubst (val, var) a
      b' <- normSubst (val, var) b
      pure $ NormImplDep var' a' b'
  NormArr a b -> do
      a' <- normSubst (val, var) a
      b' <- normSubst (val, var) b
      pure $ NormArr a' b'
  -- NormSig [(String, TypeNormal)]

  
neuSubst :: (TypeNormal, String) -> TypeNeutral -> EvalM TypeNormal
neuSubst (val, var) ty = case ty of 
  NeuVar var' ->
    if var == var' then
      pure val
    else 
      pure $ Neu (NeuVar var')
  NeuApp l r -> do
    l' <- neuSubst (val, var) l
    r' <- normSubst (val, var) r
    case r' of 
      Neu n -> pure $ Neu (NeuApp n r')
      NormDep var a b -> do
        if t_hasType r' a then
          normSubst (r', var) b
        else
          throwError "bad type application"
  -- NeuDot sig field -> do
  --   sig' <- neuSubst 

instance Eq TypeNormal where  
  a == b = norm_equiv a b (Set.empty, 0) (Map.empty, Map.empty)


-- TODO: add η reductions to the equality check
norm_equiv :: TypeNormal -> TypeNormal -> Generator -> (Map.Map String String, Map.Map String String)
        -> Bool 
norm_equiv (NormUniv n1) (NormUniv n2) gen rename = n1 == n2
norm_equiv (Neu n1) (Neu n2) gen rename = neu_equiv n1 n2 gen rename
norm_equiv (NormPrim p1) (NormPrim p2) _ _ = p1 == p2

-- Note: arrows and dependent types /can/ be equivalent if the bound variable
-- doesn't come on the LHS
norm_equiv (NormDep var a b) (NormDep var' a' b') gen (lrename, rrename) = 
  let (nvar, gen') = genFresh gen
  in (a == a') && (norm_equiv b b'
                   (useVars [var, var', nvar] gen')
                   (Map.insert var nvar lrename, Map.insert var' nvar rrename))
norm_equiv (NormArr a b)     (NormArr a' b') gen rename = 
  (norm_equiv a a' gen rename) || (norm_equiv b b' gen rename)
norm_equiv (NormDep var a b) (NormArr a' b') gen rename = 
  if Set.member var (free b) then
    False
  else
    norm_equiv a a' gen rename && norm_equiv b b' gen rename
norm_equiv (NormArr  a b) (NormDep var' a' b') gen rename = 
  if Set.member var' (free b') then
    False
  else
    norm_equiv a a' gen rename && norm_equiv b b' gen rename
-- norm_equiv (NormImplDep var a b) (NormImplDep var' a' b') gen rename = 
--   (var a b) || ()



  
neu_equiv :: TypeNeutral -> TypeNeutral -> Generator -> (Map.Map String String, Map.Map String String)
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
