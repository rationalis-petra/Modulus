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
  inferVar)                          
  
  where

import Debug.Trace
import Data (PrimType(..),
             Normal,
             Normal'(..),
             Core(..),
             Neutral,
             Neutral'(..),
             CollTy(..),
             CollVal(..),
             var_counter,
             EvalM)

import qualified Typecheck.Context as Ctx
import qualified Interpret.Eval as Eval
import Interpret.EvalM
import Syntax.Utils (typeVal, free, getField)
import Control.Monad.Except (Except, runExcept)

import qualified Data.Map as Map  
import qualified Data.Set as Set  

err = throwError  

type LRSubst = ([(Normal, String)], [(Normal, String)])
type Subst = [(Normal, String)]

-- NOTICE: this module will be deprecated in terms of unify

-- Constrain: similar to unification, but with significant enough differences
-- that I've renamed it for clarity. The differences are:
--   + Instead of t1[subst] = t2[subst], we have t1[subst] <: t2[subst]. 
--   + It returns a two list of applications l1, l2, which should be applied to
--     the corresponding in order which h

-- In constrainl(constrainr), we unify variables we are inferring (integers),
-- but the substitution of dependently-bound (string) variables occurs only on
-- the left(right) side

constrain :: Normal -> Normal -> Ctx.Context -> EvalM ([Normal], [Normal], Subst)
constrain n1 n2 ctx = do
  (lapp, rapp, subst) <- constrainLRApp n1 n2 ctx
  pure (lapp, rapp, toSing subst)


-- constrainLRApp :: Normal -> Normal -> EvalM ([Normal], [Normal], LRSubst)
-- TODO: If they are both an implicit apply, may need to re-abstract and
--   substitute in neutral variables (as done in TApply). For now, just move straight to constrain' 
-- TODO: we need to perform a renaming in variable-capturing forms, so that we can constrain, e.g.  
-- List [A] and {A} → List A by first renaming List [A] & {S} → List S then performing application
-- ({S} → List S) {A} to get List [A] and List [A]!!

-- Note: constrainLRApp doesn't actually check the types!  
constrainLRApp :: Normal -> Normal -> Ctx.Context -> EvalM ([Normal], [Normal], LRSubst)
constrainLRApp (NormImplProd s a b) (NormImplProd s' a' b') ctx = do
  subst <- constrain' b b'
  pure ([], [], subst)
constrainLRApp (NormImplProd s a b) (Neu (NeuVar v)) ctx = do
  if occurs v (NormImplProd s a b) then  
    err "occurs check failed"
  else 
    pure ([], [], rightsubst (NormImplProd s a b) v)
constrainLRApp (NormImplProd s a b)    r ctx = do
  (a1, a2, subst) <- constrainLRApp b r ctx
  appval <- case findLStrSubst s subst of  
    Just v -> inferVar v a ctx
    Nothing -> err ("cannot find implicit substitution for var " <> s <> " constraining terms: " 
                    <> show (NormImplProd s a b) <> " and "
                    <> show r
                    <> " in substitution: " <> show subst)
  pure ((appval:a1), a2, rmLSubst s subst)

  
constrainLRApp (Neu (NeuVar v)) (NormImplProd s' a' b') ctx = do
  if occurs v (NormImplProd s' a' b') then  
    err "occurs check failed"
  else 
    pure ([], [], leftsubst (NormImplProd s' a' b') v)
constrainLRApp l (NormImplProd s' a' b') ctx = do
  (a1, a2, subst) <- constrainLRApp l b' ctx
  appval <- case findRStrSubst s' subst of  
    Just v -> inferVar v a' ctx
    Nothing -> err ("cannot find implicit substitution for var " <> s' <> " constraining terms: " 
                    <> show l <> " and "
                    <> show (NormImplProd s' a' b')
                    <> " in substitution: " <> show subst)
  pure (a1, (appval:a2), rmRSubst s' subst)
constrainLRApp l r ctx = do
  subst <- constrain' l r
  pure ([], [], subst)

  
constrain' :: Normal -> Normal -> EvalM LRSubst
constrain' (Neu (NeuVar v1)) (Neu (NeuVar v2)) =
    if v1 == v2 then pure lrnosubst
    else pure (rightsubst (Neu $ NeuVar v1) v2)
constrain' (Neu n) ty = nnConstrain n ty
constrain' ty (Neu n) = do
  -- TODO: technically not respecting subtyping rules ()
  (l, r) <- nnConstrain n ty
  pure (r, l)

constrain' (PrimVal p1) (PrimVal p2) =
  if p1 == p2 then pure lrnosubst else err ("non-equal primitives in constrain: "
                                            <> show p1 <> " and " <> show p2)
constrain' (PrimType p1) (PrimType p2) =
  if p1 == p2 then pure lrnosubst else err ("non-equal primitives in constrain: "
                                            <> show p1 <> " and " <> show p2)
constrain' (CollTy (ListTy a)) (CollTy (ListTy b)) = do
  constrain' a b
  
constrain' (NormUniv n1) (NormUniv n2) =
  if n1 == n2 then pure lrnosubst else err ("non-equal primitives in constrain"
                                            <> show (NormUniv n1) <> " and " <> show (NormUniv n2))

constrain' (NormArr l1 r1) (NormArr l2 r2) = do
  -- remember: function subtyping is contravaraiant in the argument and
  -- covariant in the return type
  s1 <- constrain' l2 l1
  s2 <- constrain' r1 r2
  composelr (swap s1) s2

constrain' (NormProd str l1 r1) (NormProd str' l2 r2) =
  -- TODO: is dependent subtyping is contravaraiant in the argument and
  -- covariant in the return type
  if str == str' then do
    s1 <- constrain' l2 l1
    checkSubst "error: constrain attempting substitution for dependently bound type" str s1
    s2 <- constrain' r1 r2 
    composelr (swap s1) s2
  else
    err "cannot constrain dependent types with unequal arg"

constrain' (NormImplProd str l1 r1) (NormImplProd str' l2 r2) =
  -- TODO: same as above (dependent)
  if str == str' then do
    s1 <- constrain' l2 l1
    checkSubst "error: constrain attempting substitution for implicit dependently bound type" str s1
    s2 <- constrain' r1 r2 
    composelr (swap s1) s2
  else
    err "cannot constrain dependent types with unequal arg"

constrain' (NormSig m1) (NormSig m2) = 
  -- TODO: look out for binding of field-names to strings!!
  foldr (\(k, ty1) mnd ->
                      case getField k m2 of
                        Just ty2 -> do
                          s1 <- mnd
                          s2 <- constrain' ty1 ty2
                          composelr s1 s2 
                        Nothing -> err ("cannot constrain types, as rhs does not have field " <> k))
    (pure lrnosubst) m1

  
constrain' (NormSct m1 t1) (NormSct m2 t2) = 
  -- TODO: look out for binding of field-names to strings!!
  foldr (\(k, ty1) mnd ->
                      case getField k m2 of
                        Just ty2 -> do
                          s1 <- mnd
                          s2 <- constrain' ty1 ty2
                          composelr s1 s2 
                        Nothing -> err ("cannot constrain structures, as rhs does not have field " <> k))
    (pure lrnosubst) m1


constrain' (NormIVal name1 tyid1 id1 _ vals1 norm1) (NormIVal name2 tyid2 id2 _ vals2 norm2) =
  if tyid1 == tyid2 && id1 == id2 then
    foldr (\(n1, n2) mnd -> do
              s1 <- mnd
              s2 <- constrain' n1 n2
              composelr s1 s2)
      (pure lrnosubst) (zip vals1 vals2)
  else
    err "cannot constrain inductive values of non-equal constructors"

constrain' (NormIType name1 id1 vals1) (NormIType name2 id2 vals2) =
  if id1 == id2 then
    foldr (\(n1, n2) mnd -> do
              s1 <- mnd
              s2 <- constrain' n1 n2
              composelr s1 s2)
      (pure lrnosubst) (zip vals1 vals2)
  else
    err "cannot constrain inductive datatypes of non-equal constructors"
constrain' (CollTy t1) (CollTy t2) =   
  case (t1, t2) of 
    (IOMonadTy l, IOMonadTy r) -> constrain' l r

constrain' t1 t2 =   
  err ("cannot constrain terms " <> show t1 <> " and " <> show t2 <> " as they have different forms")

-- nn constrain: constrain a neutral and normal term  
nnConstrain :: Neutral -> Normal -> EvalM LRSubst
nnConstrain (NeuVar v) norm = pure $ leftsubst norm v
nnConstrain n1 (Neu n2) = neuConstrain n1 n2
nnConstrain (NeuDot neu field) norm = do
  normTy <- liftExcept $ typeVal norm 
  nnConstrain neu (NormSct [(field, norm)] normTy)
nnConstrain n1 n2 = err ("nnConstrain incomplete OR terms " <> show n1 <> " and " <> show n2
                          <> "have different forms")


-- neuconstrain: constrain two neutral terms  
neuConstrain :: Neutral -> Neutral -> EvalM LRSubst
neuConstrain n1 n2 = err ("neuConstrain incomplete OR terms " <> show n1 <> " and " <> show n2
                          <> "have different forms")




  
-- Substitution Utilities  
-- recall 
-- Subst = (Map.Map Int Normal, Map.Map String Normal)
-- we need to be able to join and query these substitutions

nosubst :: Subst
nosubst = []

lrnosubst :: LRSubst
lrnosubst = ([], [])
leftsubst :: Normal -> String -> LRSubst
leftsubst ty s = ([(ty, s)], [])
rightsubst :: Normal -> String -> LRSubst
rightsubst ty s =  ([], [(ty, s)])


findStrSubst :: String -> Subst -> Maybe Normal
findStrSubst str ((ty, str') : ss) =
  if str == str' then Just ty
  else findStrSubst str ss
findStrSubst _ [] = Nothing

rmSubst :: String -> Subst -> Subst
rmSubst str ((ty, str') : ss)=
  if str == str' then rmSubst str ss
  else let ss' = rmSubst str ss in ((ty, str') : ss')
rmSubst str [] = []

findLStrSubst :: String -> LRSubst -> Maybe Normal
findLStrSubst str (l, _) = findStrSubst str l

findRStrSubst :: String -> LRSubst -> Maybe Normal
findRStrSubst str (_, r) = findStrSubst str r

rmLSubst :: String -> LRSubst -> LRSubst
rmLSubst str (l, r) = (rmSubst str l, r)

rmRSubst :: String -> LRSubst -> LRSubst
rmRSubst str (l, r) = (l, rmSubst str r)
  

-- composition of substitutions: For HM substitutions, they are run in order,
-- while for the string-based substitutions, we don't know in what order they
-- are run
-- thus, to compose s1 with s2
-- 1: we apply all of s1's HM substitutions to s2
-- 2: we append  of s1's string substitutions to s2's string substitutions
compose :: Subst -> Subst -> EvalM Subst
  -- TODO SEEMS DODGY!!
compose str1 str2 = pure $ str1 <> str2
-- compose (s : ss, str1) (s2, str2) =
--   let iter :: (Normal, String) -> [(Normal, a)] -> EvalM [(Normal, a)]
--       iter s [] = pure []
--       iter s ((ty, vr) : ss) = do
--         ty' <- Type.normSubst s ty
--         tl <- iter s ss
--         pure $ (ty', vr) : tl
--   in do
--     -- perform substitution s within s2 
--     tl <- iter s s2 
--     compose (ss, str1) (s : tl)

composeList [] = pure nosubst
composeList (s:ss) = do
  cmp <- composeList ss
  compose s cmp

  -- TODO: fix!
composelr :: LRSubst -> LRSubst -> EvalM LRSubst
composelr (l1, r1) (l2, r2) = pure (l1 <> l2, r1 <> r2)
-- composelr (l1, r1) (l2, r2) =
--   let iter :: (Normal, String) -> [(Normal, a)] -> EvalM [(Normal, a)]
--       iter s [] = pure []
--       iter s ((ty, vr) : ss) = do
--         hd <- Eval.normSubst s ty
--         tl <- iter s ss
--         pure $ (hd, vr) : tl
--   in do
--     l' <- iter l1 l2
--     r' <- iter r1 r2
--     -- perform substitution s within s2 
--     composelr (l', r')

-- convert a lr substitution to a single substitution
-- TODO: this is BAD - we need to check for redundancy!
toSing  :: LRSubst -> Subst
toSing (left, right) = (left <> right)

-- Perform substitution
-- TODO: do what about order of string substitution? rearranging??
doSubst :: Subst -> Normal  -> EvalM Normal 
doSubst subst ty = case subst of 
  [] -> pure ty 
  ((sty, s) : ss) -> do
    ty' <- Eval.normSubst (sty, s) ty
    doSubst ss ty'

-- Throw an error if a variable (string) is contained in a substitution
checkSubst :: String -> String -> LRSubst -> EvalM ()
checkSubst msg str (l, r) = checkSubst' str (l <> r)
  where
    checkSubst' _ [] = pure ()
    checkSubst' str ((ty, str') : ss) = 
      if str == str' then 
        err msg
      else 
        checkSubst' str ss


-- TODO: we need to shadow bound variables!!
-- Occurs Check: given a variable x and a type t, x occurs in t 
-- if some subterm of t is equal to x and x is not equal to t
occurs :: String -> Normal -> Bool
occurs _ (Neu (NeuVar _)) = False
occurs v t = occurs' v t

-- OccursCheck': Subtly different from occurs, this algorithm is recursive:
-- occurs' is true for variable v and type t if v = t or occurs' is
-- true for v any subterms in t
occurs' :: String -> Normal -> Bool
occurs' v1 (Neu neu) = occursNeu v1 neu
  -- Primitive types and values
occurs' _ (PrimVal _) = False
occurs' _ (PrimType _) = False

-- Universes   
occurs' _ (NormUniv _) = False

occurs' v (NormArr t1 t2) = occurs' v t1 || occurs' v t2
occurs' v (NormProd str t1 t2) = -- remember: dependent type binding can shadow!
  if v == str then
    occurs' v t1
  else
    occurs' v t1 || occurs' v t2
occurs' v (NormImplProd str t1 t2) = -- remember: dependent type binding can
  -- shadow!
  if v == str then occurs' v t1 else occurs' v t1 || occurs' v t2
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
    occursFields ((v', val) : fields) =
      if v == v' then False else (occurs' v val) || (occursFields fields)

occurs' v (NormIType _ _ params) = foldr (\ty b -> b || occurs' v ty) False params
occurs' v (NormIVal _ _ _ _ params _) = -- TODO: check if we need to ask about free vars in the type??
  foldr (\ty b -> b || occurs' v ty) False params


occursNeu :: String -> Neutral -> Bool   
occursNeu v1 (NeuVar v2) = v1 == v2
occursNeu v (NeuApp l r) = occursNeu v l || occurs' v r
occursNeu v (NeuDot m _) = occursNeu v m
occursNeu v (NeuIf c e1 e2) = occursNeu v c || occurs' v e1 || occurs' v e2


-- Given a type and a substitution (thus far), try and infer the variable
inferVar :: Normal -> Normal -> Ctx.Context -> EvalM Normal
inferVar n ty ctx = do
  ty' <- liftExcept $ typeVal n
  let bl = subType ty ty'
  if bl then
    pure n
  else
    deduceVal n ty ctx

-- TODO: how to deal with signatures of types??
deduceVal :: Normal -> Normal -> Ctx.Context -> EvalM Normal
deduceVal (NormSct fields1 sctty) (NormSig tyfields) ctx = 
  let delta = foldr (\(k, _) fs -> case getField k fields1 of
                        Just x -> fs
                        Nothing -> k : fs) [] tyfields 
  in
    if null delta then
      pure (NormSct fields1 sctty)
    -- try and add missing fields
    else 
      let valMatch :: Normal -> Bool
          valMatch (NormSct candFields candTy) = do
            -- given a candidate with feilds candidate fields, we need to ensure:
            -- a) For each field in the derived part of the value, the candidate
            --    has a corresponding field of equal value (parMatch)
            -- b) The candidate has type of the signature (subType)
            let parMatch [] _ = True
                parMatch ((k, v):xs) rhs = case getField k rhs of
                  Just v' -> v == v' && parMatch xs rhs
                  Nothing -> False
            (parMatch fields1 candFields) && subType (NormSig tyfields) candTy 
          valMatch _ = False
          
          f1 val accum = case accum of 
            Right Nothing -> if valMatch val then Right $ Just val else Right Nothing
            Right (Just x) ->
              if valMatch val then
                Left "ambigous implicit module resolution"
              else
                Right $ Just x
            Left err -> Left err

          -- TODO: what about let-bindings of constants/structures, then are
          -- they implicit?
          f2 _ _ accum = accum 
      in
        case Ctx.fold f1 f2 (Right Nothing) ctx of
          Right (Just v) -> pure v
          Right Nothing -> throwError ("cannot find value of type: "
                                       <> show (NormSig tyfields)
                                       <> "\npartially matching "
                                       <> show (NormSct fields1 sctty))
          Left err -> throwError err
deduceVal v1 v2 _ = throwError ("deduce val used for non-struct values " <> show v1 <> " and " <> show v2)


  
subType :: Normal -> Normal -> Bool
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
subType (Neu n1) (Neu n2) = Eval.neu_equiv n1 n2 (Set.empty, 0) (Map.empty, Map.empty)
-- value forms  
subType (PrimVal p1) (PrimVal p2) = p1 == p2
subType _ _ = False

swap (a, b) = (b, a)
