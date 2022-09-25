module Syntax.Utils where

import Data
import Control.Monad.Except (Except, throwError, catchError)

import qualified Data.Map as Map
import qualified Data.Set as Set

  
getField :: Eq a => a -> [(a, b)] -> Maybe b
getField _ [] = Nothing
getField key ((key', val) : fields) = 
  if key == key' then
    Just val
  else 
    getField key fields

hasField :: Eq a => a -> [(a, b)] -> Bool
hasField _ [] = False
hasField key ((key', _) : fields) = 
  if key == key' then
    True
  else 
    hasField key fields

delete :: Eq a => a -> [(a, b)] -> [(a, b)]
delete key [] = []
delete key ((k, v) : tl) =
  if key == k then
    delete key tl
  else
    (k, v) : delete key tl

addField :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
addField key val fields = 
  (key, val) : delete key fields
  
insertLeft :: Eq a => [(a, b)] -> [(a, b)] -> [(a, b)]
insertLeft left right =  
  foldr (uncurry addField) left right

restrict :: Eq a => [(a, b)] -> [(a, c)] -> [(a, b)]
restrict [] sig = []
restrict ((k, v) : tail) sig =
  case getField k sig of 
    Just _  -> (k, v) : restrict tail sig
    Nothing -> restrict tail sig




  

typeVal :: Normal -> Except String Normal
typeVal (PrimType e) = pure $ NormUniv 0
typeVal (PrimVal e) = pure (PrimType (typePrim e))
  where
    typePrim :: PrimVal -> PrimType 
    typePrim e = case e of 
      Unit -> UnitT
      Bool _ -> BoolT
      Int _ -> IntT
      Nat _ -> NatT
      Float _ -> FloatT
      Char _ -> CharT
      String _ -> StringT
typeVal (InbuiltCtor ctor) = case ctor of 
  IndPat _ _ _ _ ty -> pure ty
typeVal (NormCoVal _ ty) = pure ty
typeVal (NormCoDtor _ _ _ _ _ _ ty) = pure ty

-- type of types
typeVal (NormUniv k) = pure (NormUniv (k + 1))
typeVal (NormIType _ _ _) = pure (NormUniv 0)
typeVal (NormArr _ _) = pure (NormUniv 0)
typeVal (NormProd _ _ _) = pure (NormUniv 0)
typeVal (NormImplProd _ _ _) = pure (NormUniv 0)
typeVal (NormSig _) = pure (NormUniv 0)

-- Functions
typeVal (Builtin _ ty) = pure ty
typeVal (NormAbs _ _ ty) = pure ty
typeVal (NormSct m ty) = pure ty

typeVal (NormIVal _ _ _ _ _ ty) = pure ty
typeVal (CollTy _) = pure $ NormUniv 0
typeVal (CollVal val) = case val of
  IOAction _ ty -> pure ty
  ListVal _ ty -> pure (CollTy (ListTy ty))
  ArrayVal _ ty dims -> pure (CollTy (ArrayTy ty dims))

typeVal (Neu _ ty) = pure ty
typeVal e = throwError $ "untypable value: " <> show e


        




class Expression a where
  free :: a -> Set.Set String
  rename :: String -> String -> a -> a
  

-- TODO: should type annotations be included in free???
instance Expression (Normal' m) where 
  free (Builtin _ _) = Set.empty
  free (PrimType  _) = Set.empty
  free (NormUniv  _) = Set.empty
  free (PrimVal   _) = Set.empty
  free (CollTy ty) = case ty of 
    ListTy a -> free a
    ArrayTy a _ -> free a
    IOMonadTy a -> free a
  free (CollVal val) = case val of 
    ListVal lst ty -> foldr (Set.union . free) (free ty) lst
    IOAction _ ty -> free ty

  free (Neu neutral ty) = Set.union (free neutral) (free ty)
  free (NormProd var a b) =
    Set.union (free a) (Set.delete var (free b))
  free (NormImplProd var a b) =
    Set.union (free a) (Set.delete var (free b))
  free (NormArr a b) =
    Set.union (free a) (free b)
  free (NormIVal _ _ _ _ norms ty) = foldr (Set.union . free) Set.empty norms
  free (NormIType _ _ norms) = foldr (Set.union . free) Set.empty norms
  free (NormSig fields) = foldl (\set (field, val) ->
                                   Set.delete field (Set.union (free val) set)) Set.empty fields

  rename s1 s2 norm = case norm of
    (Neu neutral ty) -> Neu (rename s1 s2 neutral) (rename s1 s2 ty)
    (Builtin fn ty) -> Builtin fn (rename s1 s2 ty)
    (PrimType  t)   -> PrimType t
    (NormUniv  u)   -> NormUniv u
    (PrimVal   v)   -> PrimVal v
    (CollTy ty) -> CollTy $ case ty of 
      ListTy a -> ListTy $ rename s1 s2 a
      ArrayTy a idx -> ArrayTy (rename s1 s2 a) idx
      IOMonadTy a -> IOMonadTy $ rename s1 s2 a
    (CollVal val) -> CollVal $ case val of 
      ListVal lst ty -> ListVal (map (rename s1 s2) lst) (rename s1 s2 ty) 
      IOAction action ty -> IOAction action (rename s1 s2 ty)

    (NormProd var a b) ->
      if var == s1 then
        NormProd var (rename s1 s2 a) b
      else 
        NormProd var (rename s1 s2 a) (rename s1 s2 b)
    (NormImplProd var a b) ->
      if var == s1 then
        NormImplProd var (rename s1 s2 a) b
      else 
        NormImplProd var (rename s1 s2 a) (rename s1 s2 b)
    (NormArr a b) -> NormArr (rename s1 s2 a) (rename s1 s2 b)
    -- (NormIVal _ _ _ _ norms ty) = foldr (Set.union . rename) Set.empty norms
    -- (NormIType _ _ norms) = foldr (Set.union . rename) Set.empty norms
    (NormSig fields) ->
      NormSig (renameFields fields)
      where renameFields [] = []
            renameFields ((field, val):fields) = 
              if field == s1 then
                (field, val):fields
              else 
                (field, rename s1 s2 val):renameFields fields


instance Expression (Neutral' m) where
  free (NeuVar var ty) = Set.insert var (free ty)
  free (NeuApp l r) = (free l) <> (free r)
  free (NeuDot sig field) = (free sig)
  free (NeuIf cond e1 e2 ty) = free cond <> free e1 <> free e2 <> free ty
  free (NeuMatch term alts ty) =
      free term <> (foldr (Set.union . altfree) Set.empty alts) <> free ty
    where
      altfree (p, e) = foldr (Set.delete) (patVars p) (free e)
  free (NeuBuiltinApp _ _ _) = Set.empty

  rename s1 s2 neu = case neu of  
    (NeuVar var ty) ->
      if var == s1 then
        NeuVar s2 (rename s1 s2 ty)
      else
        NeuVar var (rename s1 s2 ty)
    (NeuApp l r) -> NeuApp (rename s1 s2 l) (rename s1 s2 r)

patVars :: Pattern -> Set.Set String
patVars WildCard = Set.empty
patVars (VarBind sym _) = Set.singleton sym
patVars (MatchInduct id1 id2 subpats) = foldr Set.union Set.empty (map patVars subpats)

mkVar s = Neu (NeuVar s (NormUniv 0)) (NormUniv 0)

freshen :: Set.Set String -> String -> String
freshen set str = 
  if Set.member str set then
    freshen set ("*" <> str) 
  else
    str


