module Typecheck.TypeUtils where

import Data (Value(..),
             PrimE(..),
             EffectType(..),
             ModulusType(..),
             PrimType(..))
import Typecheck.InfType
import Control.Monad.Except (Except, throwError, catchError)

import qualified Data.Map as Map
import qualified Data.Set as Set

typeExpr :: (Value m) -> Except String ModulusType
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
typeExpr (CFunction _ _ ctx ty) = pure ty
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



hasType :: (Value m) -> ModulusType -> Bool
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
      let (Signature substSig) = foldr (\(k, t) sig -> doSubstMls (t, k) sig) (Signature sig) mtypes
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

infGetFree :: InfType -> Set.Set (Either String Int) -> Set.Set (Either String Int)
infGetFree (IMPrim _) _ = Set.empty
infGetFree (ITypeN _) _ = Set.empty
infGetFree (IMVar v) env =
  if (Set.member v env) then Set.empty else Set.singleton v
infGetFree (IMArr l r) env = 
  infGetFree l env <> infGetFree r env
infGetFree (IMDep l s r) env = 
  infGetFree l env <> infGetFree r (Set.insert (Left s) env)
infGetFree (IMImplDep l s r) env = 
  infGetFree l env <> infGetFree r (Set.insert (Left s) env)
infGetFree (IMSig sig) env = 
  let env' = Map.foldrWithKey (\str _ env -> Set.insert (Left str) env) env sig 
  in
    Map.foldr (\ty free -> Set.union (infGetFree ty env') free) Set.empty sig



 -- CONVERSIONS 
toInf :: ModulusType -> InfType  
toInf (TypeN n)            = ITypeN n
toInf (MVar sym)           = IMVar (Left sym)
toInf (Signature sig)      = IMSig (Map.map toInf sig)
toInf (MArr t1 t2)         = IMArr (toInf t1) (toInf t2)
toInf (MDep t1 sym t2)     = IMDep (toInf t1) sym (toInf t2)
toInf (ImplMDep t1 sym t2) = IMImplDep (toInf t1) sym (toInf t2)
toInf (MDot ty field)      = IMDot (toInf ty) field
toInf (MNamed id name params variants)
      = IMNamed id name (map toInf params) (map (map toInf) variants)
toInf (MEffect set ty)     = IMEffect (Set.map toInfEffect set) (toInf ty)
  where
    toInfEffect :: EffectType -> InfEffectType
    toInfEffect IOEff = IEffIO
    toInfEffect (CustomEff id args) = (ICustomEff id (map toInf args))
toInf (MPrim prim)         = IMPrim prim
toInf (MVector ty)         = IMVector (toInf ty)

toMls :: InfType -> ModulusType  
toMls (ITypeN n) = TypeN n
toMls (IMVar sym) = case sym of 
  Left str -> MVar str
  -- TODO: what if this variable occurs when not mangling?!
  Right n -> MVar ("#" <> (show n))
toMls (IMSig sig) = Signature (Map.map toMls sig)
toMls (IMArr t1 t2) = MArr (toMls t1) (toMls t2)
toMls (IMDep t1 sym t2) = MDep (toMls t1) sym (toMls t2)
toMls (IMImplDep t1 sym t2) = ImplMDep (toMls t1) sym (toMls t2)
toMls (IMDot ty field) = MDot (toMls ty) field
toMls (IMNamed id name params variants) = MNamed id name (map toMls params) (map (map toMls) variants)
toMls (IMEffect set ty) = MEffect (Set.map toMlsEffect set) (toMls ty)
  where
    toMlsEffect :: InfEffectType -> EffectType
    toMlsEffect IEffIO = IOEff 
    toMlsEffect (ICustomEff id args) = (CustomEff id (map toMls args))
toMls (IMPrim prim) = MPrim prim
toMls (IMVector ty) = MVector (toMls ty)


doSubstMls :: (ModulusType, String) -> ModulusType -> ModulusType
doSubstMls _ (TypeN n) = (TypeN n)
doSubstMls (ty, v) (MVar v') = if v == v' then ty else (MVar v')
doSubstMls (ty, v) (Signature sig) =
  Signature $ Map.mapWithKey (\var t -> if var == v then t else doSubstMls (ty, v) t) sig
doSubstMls s (MArr t1 t2) = MArr (doSubstMls s t1) (doSubstMls s t2)
doSubstMls (ty, v) (MDep t1 v' t2) =
  MDep (doSubstMls (ty, v) t1) v' (if v == v' then t2 else doSubstMls (ty, v) t2)
doSubstMls (ty, v) (ImplMDep t1 v' t2) =
  ImplMDep (doSubstMls (ty, v) t1) v' (if v == v' then t2 else doSubstMls (ty, v) t2)
doSubstMls s (MDot ty field) = 
  case doSubstMls s ty of
    Signature m -> case Map.lookup field m of 
      Just ty -> ty
    ty' -> (MDot ty' field)
-- MEffect (Set.Set EffectType) ModulusType
--  MNamed Int String [ModulusType] [[ModulusType]]
doSubstMls _ (MPrim p) = MPrim p
doSubstMls s (MVector ty) = MVector (doSubstMls s ty)
-- Undef
-- Large


