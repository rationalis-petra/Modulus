{-# LANGUAGE FlexibleContexts #-}
module Typecheck.Constrain (
  Subst,
  LRSubst,
  constrain,
  nosubst,
  compose,
  composeList,
  rmSubst,
  findStrSubst,
  doSubst,
  varLeft,
  varRight,
  inferVar)
  where


import qualified Data.Map as Map  
import qualified Data.Set as Set  
import Control.Monad.Reader (MonadReader, ask)
import Control.Monad.State  (MonadState)
import Control.Monad.Except (MonadError, throwError)

import Syntax.Expression(free, rename)
import Syntax.Normal (PrimType(..),
                      Normal(..),
                      Neutral(..),
                      CollTy(..),
                      CollVal(..),
                      ArgType(..),
                      ProgState,
                      var_counter)
import Syntax.Core(Core(..))

import qualified Interpret.Environment as Env
import Interpret.Environment (Environment)
import qualified Interpret.Eval as Eval
import Interpret.Eval (normSubst)
import Interpret.EvalM
import Syntax.Utils (typeVal, getField, freshen)
import Control.Monad.Except (Except, runExcept)

type LRSubst m = ([(Normal m, String)], [(Normal m, String)], [((String, Normal m), (String, Normal m))])
type Subst m = ([(Normal m, String)], [((String, Normal m), (String, Normal m))])

-- NOTICE: this module will be deprecated in terms of unify

-- Constrain: similar to unification, but with significant enough differences
-- that I've renamed it for clarity. The differences are:
--   + Instead of t1[subst] = t2[subst], we have t1[subst] <: t2[subst]. 
--   + It returns a two list of applications l1, l2, which should be applied to
--     the corresponding in order which h

-- In constrainl(constrainr), we unify variables we are inferring (integers),
-- but the substitution of dependently-bound (string) variables occurs only on
-- the left(right) side

constrain :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) =>
             Normal m -> Normal m -> Environment m -> m ([Normal m], [Normal m], Subst m)
constrain n1 n2 env = do
  (lapp, rapp, subst) <- constrainLRApp n1 n2 env
  pure (lapp, rapp, toSing subst)


-- constrainLRApp :: Normal -> Normal -> EvalM ([Normal], [Normal], LRSubst)
-- TODO: If they are both an implicit apply, may need to re-abstract and
--   substitute in neutral variables (as done in TApply). For now, just move straight to constrain' 
-- TODO: we need to perform a renaming in variable-capturing forms, so that we can constrain, e.g.  
-- List [A] and {A} → List A by first renaming List [A] & {S} → List S then performing application
-- ({S} → List S) {A} to get List [A] and List [A]!!

-- Note: constrainLRApp doesn't actually check the types!  
-- TODO: perform α-renaming on implicit products!  
constrainLRApp :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m -> Normal m -> Environment m -> m ([Normal m], [Normal m], LRSubst m)
constrainLRApp (NormProd s1 Hidden a1 b1) (NormProd s2 Hidden a2 b2) ctx = do
  subst <- constrain' b1 b2
  pure ([], [], subst)

constrainLRApp (NormProd s Hidden a b) (Neu (NeuVar v _) _) ctx = do
  if occurs v (NormProd s Hidden a b) then  
    throwError "occurs check failed"
  else 
    pure ([], [], rightsubst (NormProd s Hidden a b) v)

constrainLRApp (NormProd s Hidden a b)    r ctx = do
  let s' = freshen (Set.union (free b) (free r)) s
  b' <- normSubst ((Neu (NeuVar s' a) a), s) b
  (a1, a2, subst) <- constrainLRApp b' r ctx
  appval <- case findLStrSubst s' subst of  
    Just v -> inferVar v a ctx
    Nothing -> throwError ("cannot find implicit substitution for var " <> s' <> " constraining terms: " 
                    <> show (NormProd s' Hidden a b') <> " and "
                    <> show r
                    <> " in substitution: " <> show subst)
  let subst' = rmLSubst s' subst
      fnlSubst = renameLSubst s' s subst'
  pure ((appval:a1), a2, fnlSubst)

constrainLRApp (Neu (NeuVar v _) _) (NormProd s' Hidden a' b') ctx = do
  if occurs v (NormProd s' Hidden a' b') then  
    throwError "occurs check failed"
  else 
    pure ([], [], leftsubst (NormProd s' Hidden a' b') v)

constrainLRApp l (NormProd s Hidden a b) ctx = do
  let s' = freshen (Set.union (free b) (free l)) s
  b' <- normSubst ((Neu (NeuVar s' a) a), s) b
  (a1, a2, subst) <- constrainLRApp l b' ctx
  appval <- case findRStrSubst s' subst of  
    Just v -> inferVar v a ctx
    Nothing -> throwError ("cannot find implicit substitution for var " <> s' <> " constraining terms: " 
                    <> show l <> " and "
                    <> show (NormProd s' Hidden a b')
                    <> " in substitution: " <> show subst)
  let subst' = rmLSubst s' subst
      fnlSubst = renameLSubst s' s subst'
  pure (a1, (appval:a2), fnlSubst)

constrainLRApp l r ctx = do
  subst <- constrain' l r
  pure ([], [], subst)

  
constrain' :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m -> Normal m -> m (LRSubst m)

constrain' (Neu (NeuVar v1 t1) _) (Neu (NeuVar v2 t2) _) =
    if v1 == v2 then pure lrnosubst
    else pure (varsame (v1, t1) (v2, t2))

constrain' (Neu n _) ty = nnConstrain n ty

constrain' ty (Neu n _) = do
  -- TODO: technically not respecting subtyping rules ()
  subst <- nnConstrain n ty
  pure (swap subst)

constrain' (PrimVal p1) (PrimVal p2) =
  if p1 == p2 then pure lrnosubst else throwError ("non-equal primitives in constrain: "
                                            <> show p1 <> " and " <> show p2)
constrain' (PrimType p1) (PrimType p2) =
  if p1 == p2 then pure lrnosubst else throwError ("non-equal primitives in constrain: "
                                            <> show p1 <> " and " <> show p2)
constrain' (NormUniv n1) (NormUniv n2) =
  if n1 == n2 then pure lrnosubst else throwError ("non-equal primitives in constrain"
                                            <> show (NormUniv n1) <> " and " <> show (NormUniv n2))

constrain' (NormArr l1 r1) (NormArr l2 r2) = do
  -- remember: function subtyping is contravaraiant in the argument and
  -- covariant in the return type
  s1 <- constrain' l2 l1
  s2 <- constrain' r1 r2
  composelr (swap s1) s2

constrain' (NormProd str aty l1 r1) (NormProd str' aty' l2 r2) =
  -- TODO: perform adequate α-renaming
  if str == str' && aty == aty' then do
    s1 <- constrain' l2 l1
    checkSubst "error: constrain attempting substitution for dependently bound type" str s1
    s2 <- constrain' r1 r2 
    composelr (swap s1) s2
  else
    throwError "cannot constrain dependent types with unequal arg/visibility"

constrain' (NormSig m1) (NormSig m2) = 
  -- TODO: look out for binding of field-names to strings!!
  foldr (\(k, ty1) mnd ->
                      case getField k m2 of
                        Just ty2 -> do
                          s1 <- mnd
                          s2 <- constrain' ty1 ty2
                          composelr s1 s2 
                        Nothing -> throwError ("cannot constrain types, as rhs does not have field " <> k))
    (pure lrnosubst) m1

constrain' (NormSct m1 t1) (NormSct m2 t2) = 
  -- TODO: look out for binding of field-names to strings!!
  foldr (\(k, (ty1, _)) mnd ->
                      case getField k m2 of
                        Just (ty2, _) -> do
                          s1 <- mnd
                          s2 <- constrain' ty1 (ty2)
                          composelr s1 s2 
                        Nothing -> throwError ("cannot constrain structures, as rhs does not have field " <> k))
    (pure lrnosubst) m1

constrain' (NormIVal name1 tyid1 id1 _ vals1 norm1) (NormIVal name2 tyid2 id2 _ vals2 norm2) =
  if tyid1 == tyid2 && id1 == id2 then
    foldr (\(n1, n2) mnd -> do
              s1 <- mnd
              s2 <- constrain' n1 n2
              composelr s1 s2)
      (pure lrnosubst) (zip vals1 vals2)
  else
    throwError "cannot constrain inductive values of non-equal constructors"

constrain' (NormIType name1 id1 vals1) (NormIType name2 id2 vals2) =
  if id1 == id2 then
    foldr (\(n1, n2) mnd -> do
              s1 <- mnd
              s2 <- constrain' n1 n2
              composelr s1 s2)
      (pure lrnosubst) (zip vals1 vals2)
  else
    throwError "cannot constrain inductive datatypes of non-equal constructors"

constrain' (CollTy t1) (CollTy t2) =   
  case (t1, t2) of 
    (IOMonadTy l, IOMonadTy r) -> constrain' l r
    (ListTy    l, ListTy    r) -> constrain' l r
    (ArrayTy   l, ArrayTy   r) -> constrain' l r
    (MaybeTy   l, MaybeTy   r) -> constrain' l r
    (CPtrTy    l, CPtrTy    r) -> constrain' l r
    _ -> throwError ("cannot constrian non-matching types families: " <> show t1 <> show t2)

constrain' t1 t2 =   
  throwError ("cannot constrain terms " <> show t1 <> " and " <> show t2 <> " as they have different forms")

-- nn constrain: constrain a neutral and normal term  
nnConstrain :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Neutral m -> Normal m -> m (LRSubst m)
nnConstrain (NeuVar v _) norm = pure $ leftsubst norm v
nnConstrain n1 (Neu n2 _) = neuConstrain n1 n2
nnConstrain (NeuDot neu field) norm = do
  normTy <- typeVal norm 
  nnConstrain neu (NormSct [(field, (norm, []))] normTy)
nnConstrain n1 n2 = throwError ("nnConstrain incomplete OR terms " <> show n1 <> " and " <> show n2
                          <> " have different forms")


-- neuconstrain: constrain two neutral terms  
neuConstrain :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Neutral m -> Neutral m -> m (LRSubst m)
neuConstrain (NeuVar v1 t1) (NeuVar v2 t2) = do 
  if v1 == v2 then 
    pure lrnosubst
  else
    pure (varsame (v1, t1) (v2, t2))
neuConstrain (NeuApp neu norm) (NeuApp neu' norm') = do 
  subst1 <- neuConstrain neu neu'
  subst2 <- constrain' norm norm'
  composelr subst1 subst2
neuConstrain n1 n2 = throwError ("neuConstrain incomplete OR terms " <> show n1 <> " and " <> show n2
                          <> " have different forms")




  
-- Substitution Utilities  
-- recall 
-- Subst = (Map.Map Int Normal, Map.Map String Normal)
-- we need to be able to join and query these substitutions

nosubst :: Subst m
nosubst = ([], [])

swap :: LRSubst m -> LRSubst m
swap (l, r, s) = (r, l, map (\(x, y) -> (y, x)) s)


lrnosubst :: LRSubst m
lrnosubst = ([], [], [])


varsame :: (String, Normal m) -> (String, Normal m) -> LRSubst m
varsame s1 s2 = ([], [], [(s1, s2)])

  
leftsubst :: Normal m -> String -> LRSubst m
leftsubst ty s = ([(ty, s)], [], [])

  
rightsubst :: Normal m -> String -> LRSubst m
rightsubst ty s =  ([], [(ty, s)], [])


findStrSubst :: String -> Subst m -> Maybe (Normal m)

findStrSubst str ((ty, str') : ss, vars) =
  if str == str' then Just ty
  else findStrSubst str (ss, vars)

findStrSubst str ([], vars) = findVarSubst vars
  where
    findVarSubst [] = Nothing
    findVarSubst (((v, ty), (v', ty')) : vs) =
      if v == str then Just (Neu (NeuVar v' ty') ty')
      else findVarSubst vs

-- TODO 
rmSubst :: String -> Subst m -> Subst m
rmSubst str ((ty, str') : ss, vars)=
  if str == str' then rmSubst str (ss, vars)
  else let (ss', vars') = rmSubst str (ss, vars) in ((ty, str') : ss', vars')
rmSubst str ([], vars) = ([], vars)

  -- TODO: these are now wrong (maybe?
findLStrSubst :: String -> LRSubst  m-> Maybe (Normal m)
findLStrSubst str (l, _, vs) = findStrSubst str (l, vs)

findRStrSubst :: String -> LRSubst m -> Maybe (Normal m)
findRStrSubst str = findLStrSubst str . swap

rmLSubst :: String -> LRSubst m -> LRSubst m
rmLSubst str (l, r, v) =
  let (l', v') = rmSubst str (l, v)
  in (l', r, v')

rmRSubst :: String -> LRSubst m -> LRSubst m
rmRSubst str (l, r, v) =
  let (r', v') = rmSubst str (r, v)
  in (l, r', v')

renameLSubst :: String -> String -> LRSubst m -> LRSubst m
renameLSubst from to (l, r, v) = 
  let l' = map (\(val, var) -> if var == from then (val, to) else (val, var)) l
      r' = map (\(val, var) -> (rename from to val, var)) r 
      v' = map (substVar from to) v
  in (l', r', v')
  where 
    substVar from to ((v, t), e2) =
      let e1 = if v == from then (to, t) else (v, t)
      in (e1, e2)

renameRSubst :: String -> String -> LRSubst m -> LRSubst m
renameRSubst s1 s2 = (renameLSubst s1 s2 . swap)
  
varRight :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Subst m -> m (Subst m)
varRight (s, vars) =
  compose (s, []) (map (\((var, ty), (right, _)) -> (Neu (NeuVar var ty) ty, right)) vars, [])
  
varLeft :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Subst m -> m (Subst m)
varLeft (s, vars) =
  compose (s, []) (map (\((left, _), (var, ty)) -> (Neu (NeuVar var ty) ty, left)) vars, [])
  

-- composition of substitutions: For HM substitutions, they are run in order,
-- while for the string-based substitutions, we don't know in what order they
-- are run
-- thus, to compose s1 with s2
-- 1: we apply all of s1's HM substitutions to s2
-- 2: we append  of s1's string substitutions to s2's string substitutions
-- TODO: we need a step where we merge equivalent substitutions, e.g. 
-- [(NormSct [("x", Int)], "A"), (NormSct [("y", Int)], "A")] should merge and give
-- [(NormSct [("x", Int), ("y", Int)], "A")]

compose :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Subst m -> Subst m -> m (Subst m)
compose ([], vars) (s', vars') = pure (s', vars <> vars')
compose (s : ss, vars) (s2, vars') =
  -- iter : apply a substitution to a list of substitutions
  let iter :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => (Normal m, String) -> [(Normal m, a)] -> m [(Normal m, a)]
      iter s [] = pure []
      iter s ((ty, vr) : ss) = do
        ty' <- Eval.normSubst s ty
        tl <- iter s ss
        pure $ (ty', vr) : tl
  in do
    -- perform substitution s within s2 
    tl <- iter s s2 
    compose (ss, vars) ((s : tl), vars')

composeList s [] = pure s
composeList s1 (s2:ss) = do
  cmp <- compose s1 s2
  composeList cmp ss

  -- TODO: fix!
composelr :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => LRSubst m -> LRSubst m -> m (LRSubst m)
composelr (l1, r1, s1) (l2, r2, s2) = do
  -- iter : apply a substitution to a list of substitutions
  let iter :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => (Normal m, String) -> [(Normal m, a)] -> m [(Normal m, a)]
      iter s [] = pure []
      iter s ((ty, vr) : ss) = do
        ty' <- Eval.normSubst s ty
        tl <- iter s ss
        pure $ (ty', vr) : tl

      compose (s : ss) s2 = do
        tl <- iter s s2
        compose ss (s : tl)
      compose [] s = pure s
    in do
    -- perform substitution s within s2
      l' <- compose l1 l2
      r' <- compose r1 r2
      pure (l', r', s1 <> s2)

-- convert a lr substitution to a single substitution
-- by default, assume that 
toSing :: LRSubst m -> Subst m
toSing (left, right, vars) =
  (left <> right, vars)

-- Perform substitution
-- TODO: do what about order of string substitution? rearranging??
doSubst :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Subst m -> Normal m -> m (Normal m) 
doSubst subst ty = case subst of 
  ([], _) -> pure ty 
  (((sty, s) : ss), vrs) -> do
    ty' <- Eval.normSubst (sty, s) ty
    doSubst (ss, vrs) ty'

-- Throw an error if a variable (string) is contained in a substitution
checkSubst :: MonadError String m => String -> String -> LRSubst m -> m ()
checkSubst msg str (l, r, v) = do
  (checkSubst' str (l <> r))
  if foldr (\((s1, _), (s2, _)) b -> (str == s1 || str == s2 || b)) False v
    then throwError msg
  else
    pure ()
  where
    checkSubst' _ [] = pure ()
    checkSubst' str ((ty, str') : ss) = 
      if str == str' then 
        throwError msg
      else 
        checkSubst' str ss


-- TODO: we need to shadow bound variables!!
-- Occurs Check: given a variable x and a type t, x occurs in t 
-- if some subterm of t is equal to x and x is not equal to t
occurs :: String -> Normal m -> Bool
occurs _ (Neu (NeuVar _ _) _) = False
occurs v t = occurs' v t

-- OccursCheck': Subtly different from occurs, this algorithm is recursive:
-- occurs' is true for variable v and type t if v = t or occurs' is
-- true for v any subterms in t
occurs' :: String -> Normal m -> Bool
occurs' v1 (Neu neu _) = occursNeu v1 neu
  -- Primitive types and values
occurs' _ (PrimVal _) = False
occurs' _ (PrimType _) = False
occurs' s (CollVal val) = case val of 
  ListVal lst ty -> (foldr (\x b -> occurs' s x || b) False lst) || occurs' s ty
occurs' s (CollTy ty) = case ty of
  ListTy a -> occurs' s a

-- Universes   
occurs' _ (NormUniv _) = False

occurs' v (NormArr t1 t2) = occurs' v t1 || occurs' v t2
occurs' v (NormProd str aty t1 t2) = -- remember: dependent type binding can shadow!
  if v == str then
    occurs' v t1
  else
    occurs' v t1 || occurs' v t2
occurs' v (NormAbs var a b) =
  if v == var then occurs' v a else occurs' v a || occurs' v b

occurs' v (NormSig fields) = occursFields fields
  where
    occursFields [] = False
    occursFields ((v', ty) : fields) =
      if v == v' then False else (occurs' v ty) || (occursFields fields)
occurs' v (NormSct fields _) = occursFields fields
  where
    occursFields [] = False
    occursFields ((v', (val, _)) : fields) =
      if v == v' then False else (occurs' v val) || (occursFields fields)

occurs' v (NormIType _ _ params) = foldr (\ty b -> b || occurs' v ty) False params
occurs' v (NormIVal _ _ _ _ params _) = -- TODO: check if we need to ask about free vars in the type??
  foldr (\ty b -> b || occurs' v ty) False params


occursNeu :: String -> Neutral m -> Bool   
occursNeu v1 (NeuVar v2 _) = v1 == v2
occursNeu v (NeuApp l r) = occursNeu v l || occurs' v r
occursNeu v (NeuDot m _) = occursNeu v m
occursNeu v (NeuIf c e1 e2 _) = occursNeu v c || occurs' v e1 || occurs' v e2


-- Given a type and a substitution (thus far), try and infer the variable
inferVar :: MonadError String m => Normal m -> Normal m -> Environment m -> m (Normal m)
inferVar n ty ctx = do
  ty' <- typeVal n
  let bl = subType ty ty'
  if bl then
    pure n
  else
    deduceVal n ty ctx

-- TODO: how to deal with signatures of types??
deduceVal :: MonadError String m => Normal m -> Normal m -> Environment m -> m (Normal m)
deduceVal (NormSct fields1 sctty) (NormSig tyfields) ctx = 
  let delta = foldr (\(k, _) fs -> case getField k fields1 of
                        Just x -> fs
                        Nothing -> k : fs) [] tyfields 
  in
    if null delta then
      pure (NormSct fields1 sctty)
    -- try and add missing fields
    else 
      let --valMatch :: Normal m -> Bool
          valMatch (NormSct candFields candTy) = do
            -- given a candidate with feilds candidate fields, we need to ensure:
            -- a) For each field in the derived part of the value, the candidate
            --    has a corresponding field of equal value (parMatch)
            -- b) The candidate has type of the signature (subType)
            let parMatch [] _ = True
                parMatch ((k, (v, _)):xs) rhs = case getField k rhs of
                  Just (v', _) -> v == v' && parMatch xs rhs
                  Nothing -> False
            (parMatch fields1 candFields) && subType (NormSig tyfields) candTy 
          valMatch _ = False
          
          f val accum = case nestedSearch val accum of
            Right Nothing -> if valMatch val then Right $ Just val else Right Nothing
            Right (Just x) ->
              if valMatch val then
                Left "ambigous implicit module resolution"
              else
                Right $ Just x
            Left err -> Left err


          nestedSearch (NormSct lst _) accum = foldr f accum (map (fst . snd) lst)
          nestedSearch _ accum = accum

      in
        case Env.fold f (Right Nothing) ctx of
          Right (Just v) -> pure v
          Right Nothing ->
            throwError ("cannot find value of type: "
                        <> show (NormSig tyfields)
                        <> "\npartially matching "
                        <> show (NormSct fields1 sctty))
          Left err -> throwError err
deduceVal v1 v2 _ = throwError ("deduce val used for non-struct values " <> show v1 <> " and " <> show v2)


  
subType :: Normal m -> Normal m -> Bool
subType (NormUniv n1) (NormUniv n2) = n1 <= n2
subType (PrimType p1) (PrimType p2) = p1 == p2
subType (NormArr n1 n2) (NormArr n1' n2') = subType n1' n1 && subType n2 n2'
subType (NormSig s1) (NormSig s2) =
   foldr (\(k, v) bl -> case getField k s2 of
             Just v' -> subType v v' && bl
             Nothing -> False) True s1

-- neutral terms
-- TODO: THIS IS INCREDIBLY DODGY AND MAY BE RESPONSIBLE FOR ERRORS YOU CANT
-- FIGURE OUT!
subType (Neu n1 _) (Neu n2 _) = n1 == n2 
-- value forms  
subType (PrimVal p1) (PrimVal p2) = p1 == p2
subType _ _ = False
