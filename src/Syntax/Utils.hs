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
      Float _ -> FloatT
      Char _ -> CharT
      String _ -> StringT

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

-- typeVal (NormIType _ _ _ ty) = pure ty
typeVal (NormIVal _ _ _ _ ty) = pure ty
typeVal e = throwError $ "untypable value: " <> show e


        




class Expression a where
  free :: a -> Set.Set String
  

instance Expression (Normal' m) where 
  free (Builtin _ _) = Set.empty
  free (PrimType  _) = Set.empty
  free (NormUniv  _) = Set.empty
  free (PrimVal   _) = Set.empty

  free (Neu neutral) = free neutral
  free (NormProd var a b) =
    Set.union (free a) (Set.delete var (free b))
  free (NormImplProd var a b) =
    Set.union (free a) (Set.delete var (free b))
  free (NormArr a b) =
    Set.union (free a) (free b)
  free (NormIVal _ _ _ norms ty) = foldr (Set.union . free) Set.empty norms
  free (NormIType _ _ norms) = foldr (Set.union . free) Set.empty norms

  -- free (NormSig fields) =

instance Expression (Neutral' m) where
  free (NeuVar var) = Set.singleton var
  free (NeuApp l r) = (free l) <> (free r)
  free (NeuDot sig field) = (free sig)
  free (NeuIf cond e1 e2) = (free cond) <> (free e1) <> (free e2)
  free (NeuMatch term alts) = free term <> (foldr (Set.union . altfree) Set.empty alts)
    where
      altfree (p, e) = foldr (Set.delete) (patVars p) (free e)
    

  free (NeuDot sig field) = (free sig)
  free (NeuBuiltinApp _ _ _) = Set.empty
  free (NeuBuiltinApp2 _ _ _) = Set.empty
  free (NeuBuiltinApp3 _ _ _) = Set.empty
  free (NeuBuiltinApp4 _ _ _) = Set.empty


patVars :: Pattern -> Set.Set String
patVars WildCard = Set.empty
patVars (VarBind sym) = Set.singleton sym
patVars (MatchInduct id1 id2 subpats) = foldr Set.union Set.empty (map patVars subpats)

