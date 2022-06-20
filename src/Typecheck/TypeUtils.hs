module Typecheck.TypeUtils where

import Data (Object(..),
             PrimE(..),
             ModulusType(..),
             PrimType(..))
import Control.Monad.Except (Except, throwError, catchError)

import qualified Data.Map as Map
import qualified Data.Set as Set

typeExpr :: (Object m) -> Except String ModulusType
typeExpr (PrimE e) = pure (MPrim (typePrim e))
typeExpr (InbuiltFun _ t) = pure t
typeExpr (Type t) =
  if isLarge t then 
    pure (Large)
    -- throwError "large types do not have a type"
  else 
    pure (TypeN 1)
typeExpr (Module m) = do
  -- TODO: is this dodgy?
  lst <- mapM (\(s, v) -> typeExpr v >>= \t -> pure (s, t)) (Map.toList m)
  pure (Signature (Map.fromList lst))
typeExpr (CFunction _ _ _ ty) = pure ty
typeExpr (CConstructor _ _ _ _ _ _ ty) = pure ty
typeExpr (CustomCtor _ _ _ _ ty) = pure ty

typeExpr e = throwError $ "untypable expr: " <> show e


typePrim :: PrimE -> PrimType 
typePrim e = case e of 
  Unit -> UnitT
  Bool _ -> BoolT
  Int _ -> IntT
  Float _ -> FloatT
  Char _ -> CharT
  String _ -> StringT
  
isLarge :: ModulusType -> Bool
isLarge (TypeN _) = True
isLarge (Signature m) = Map.foldr (\x y -> (isLarge x) || y) False m
isLarge _ = False



hasType :: (Object m) -> ModulusType -> Bool
hasType (PrimE e) (MPrim t) = (typePrim e) == t
hasType (Type t) (TypeN 1) = not (isLarge t)
hasType (Module mod) (Signature sig) = 
  -- step 1: extract the large types from the signature
  let types = Map.fromList (Map.foldrWithKey (\k t lst -> if isLarge t then (k, t) : lst else lst)
                            [] sig)
  -- step 2: check to make sure that the module has these fields. If so, extract
  -- them into the mfields value
      (mtypes, hasTypes) = (Map.foldrWithKey
                              (\k t (mfields, hasTypes) ->
                                 if not hasTypes then ([], False) else
                                  case Map.lookup k mod of
                                    Just (Type v) ->
                                      if hasType (Type v) t then
                                        (((k, v) : mfields), True)
                                      else
                                        ([], False)
                                    _ -> ([], False)) ([], True) types)

  in
    if hasTypes then 
      let (Signature substSig) = foldr (\(k, t) sig -> subst k t sig) (Signature sig) mtypes
      in 
        Map.foldrWithKey (\k t b -> b && case Map.lookup k mod of 
                      Just v -> hasType v t
                      Nothing -> False) True substSig 
    else False
hasType (InbuiltFun _ t) t' = typeEq t t'
hasType (CFunction _ _ _ t) t' = typeEq t t'

hasType _ _ = False

typeEq :: ModulusType -> ModulusType -> Bool
typeEq _t1 _t2 = case (_t1, _t2) of
  (MPrim t1, MPrim t2) -> t1 == t2
  (MArr t1 t2, MArr t1' t2') -> do
    typeEq t1 t1' && typeEq t2 t2'
  (_, _) -> False

-- TODO: rename apply
-- subst is something more like an apply/reduce: it performs a limited type of
-- "evaluation"
subst :: String -> ModulusType -> ModulusType -> ModulusType
subst s t (TypeN n) = (TypeN n)
subst s t (MPrim p) = (MPrim p)
subst s t (MVar s') = if s == s' then t else (MVar s')
subst s t (MArr t1 t2) = (MArr (subst s t t1) (subst s t t2))
-- subst s t (MDep t1 s' t2) =
--   --                        TODO: should be subst here?
--   if s == s' then (MDep (subst s t t1) s' t2)
--   else (MDep (subst s t t1) s' (subst s t t2))
-- subst s t (ImplMDep t1 s' t2) =
--   --                        TODO: should be subst here?
--   if s == s' then (ImplMDep (subst s t t1) s' t2)
--   else (ImplMDep (subst s t t1) s' (subst s t t2))
subst s t (MDot t1 field) =
  case subst s t t1 of
    Signature sig -> case Map.lookup field sig of 
      Just x -> x
      -- TODO: allow throwing of errors!
      Nothing -> (MDot (Signature sig) field)
    t -> MDot t field
subst s t (Signature sig) = Signature (Map.map (subst s t) sig) 
subst s t (MNamed id name variants instances) =
  if s == name then
    MNamed id name variants instances
  else
    MNamed id name (map (subst s t) variants) (map (map (subst s t)) instances)


occursCheck :: String -> ModulusType -> Bool
occursCheck s t = case t of 
  TypeN n -> False
  MPrim p -> False
  MDot t' _ -> occursCheck s t'
  MVar s' -> s == s' 
  MArr t1 t2 -> 
    occursCheck s t1 || occursCheck s t2
  MDep t1 s' t2 -> 
    if s == s' then False else occursCheck s t1 || occursCheck s t2
  ImplMDep t1 s' t2 -> 
    if s == s' then False else occursCheck s t1 || occursCheck s t2

  -- TODO: change
  Signature map -> False
  MVector t   -> occursCheck s t


getFree :: ModulusType -> Set.Set String -> Set.Set String
getFree (MPrim _) _ = Set.empty
getFree (MVar v) env =
  if (Set.member v env) then Set.empty else Set.singleton v
getFree (MArr l r) env = 
  getFree l env <> getFree r env
getFree (MDep l s r) env = 
  getFree l env <> getFree r (Set.insert s env)
getFree (ImplMDep l s r) env = 
  getFree l env <> getFree r (Set.insert s env)
