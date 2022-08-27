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
typeVal (NormUniv k) = pure (NormUniv (k + 1))

-- Functions
typeVal (Builtin _ ty) = pure ty
typeVal (NormAbs _ _ ty) = pure ty

typeVal (NormMod m) = do
  -- TODO: is this dodgy?
  fields <- mapM (\(s, v) -> typeVal v >>= \t -> pure (s, t)) m
  pure (NormSig fields)
-- typeVal (CFunction _ _ ctx ty) = pure ty
-- typeVal (CConstructor _ _ _ _ _ _ ty) = pure ty
-- typeVal (CustomCtor _ _ _ _ ty) = pure ty
typeVal e = throwError $ "untypable value: " <> show e




t_hasType :: Normal -> Normal -> Bool
t_hasType val ty = 
  case ty of
    NormUniv k -> inUniverse val k
    NormSig fields -> hasFields val fields
    _ -> False

  where
    -- TODO: recursive definitions in type??
    hasFields :: Normal -> [(String, Normal)] -> Bool
    hasFields norm fields = 
      case norm of 
        NormSig fields' -> foldr (\(field, ty) bl ->
                                case getField field fields of 
                                  Just ty' -> t_hasType ty ty' && bl
                                  Nothing -> False) True fields'
        _ -> False

    
    inUniverse :: Normal -> Int -> Bool
    inUniverse norm k =
      case norm of  
        -- TODO: is this correct??
        --   TODO: dependent pair/signature, take max/min??
        NormUniv k' -> k' < k
        _ -> True 
        




class Expression a where
  free :: a -> Set.Set String
  

instance Expression (Normal' m) where 
  free (Neu neutral) = free neutral
  free (PrimVal _) = Set.empty
  free (PrimType _) = Set.empty
  free (NormUniv k) = Set.empty
  free (NormProd var a b) =
    Set.union (free a) (Set.delete var (free b))
  free (NormImplProd var a b) =
    Set.union (free a) (Set.delete var (free b))
  free (NormArr a b) =
    Set.union (free a) (free b)
  -- free (NormSig fields) =

instance Expression (Neutral' m) where
  free (NeuVar var) = Set.singleton var
  free (NeuApp l r) = Set.union (free l) (free r)
  free (NeuDot sig field) = (free sig)

