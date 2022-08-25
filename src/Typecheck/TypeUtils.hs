module Typecheck.TypeUtils where

import Data
import Control.Monad.Except (Except, throwError, catchError)

import qualified Data.Map as Map
import qualified Data.Set as Set

typeVal :: (Value m) -> Except String TypeNormal
typeVal (PrimVal e) = pure (NormPrim (typePrim e))
  where
    typePrim :: PrimVal -> PrimType 
    typePrim e = case e of 
      Unit -> UnitT
      Bool _ -> BoolT
      Int _ -> IntT
      Float _ -> FloatT
      Char _ -> CharT
      String _ -> StringT
typeVal (InbuiltFun _ t) = pure t
typeVal (Type ty) = pure $ NormUniv (typeSize ty)
  where
    typeSize :: TypeNormal -> Int
    typeSize (NormUniv n) = n + 1
    typeSize (NormSig fields) = foldr (\(_, x) y -> (max (typeSize x) y)) 0 fields
    typeSize _ = 1

typeVal (Module m) = do
  -- TODO: is this dodgy?
  fields <- mapM (\(s, v) -> typeVal v >>= \t -> pure (s, t)) (Map.toList m)
  pure (NormSig fields)
typeVal (CFunction _ _ ctx ty) = pure ty
typeVal (CConstructor _ _ _ _ _ _ ty) = pure ty
typeVal (CustomCtor _ _ _ _ ty) = pure ty
typeVal e = throwError $ "untypable value: " <> show e


-- typeαEq :: TypeVal -> TypeVal -> Bool
-- typeαEq _t1 _t2 = case (_t1, _t2) of
--   (ValPrim t1, ValPrim t2) -> t1 == t2
--   (Universe n1, Universe n2) -> n1 == n2
--   (ValArr t1 t2, ValArr t1' t2') -> do
--     typeαEq t1 t1' && typeαEq t2 t2'


-- getFree :: TypeVal -> Set.Set String -> Set.Set String
-- getFree (ValPrim _) _ = Set.empty
-- getFree (ValArr l r) taken = 
--   getFree l taken <> getFree r taken
-- getFree (ValDep s ty body env) taken =
--   getFree ty taken <> getFreeTyExpr body (Set.insert (fromString s) (toTaken env))
-- getFree (ValImplDep s ty body env) taken = 
--   getFree ty taken <> getFreeTyExpr body (Set.insert (fromString s) (toTaken env))

-- getFreeTyExpr :: TypeExpr -> Set.Set String -> Set.Set String
-- getFreeTyExpr (TyVal ty) taken = getFree ty taken
-- getFreeTyExpr (TyVar v) taken =
--   if (Set.member v taken) then Set.empty else Set.singleton v
-- getFreeTyExpr (TyArr l r) taken =
--   getFreeTyExpr l taken <> getFreeTyExpr r taken
-- getFreeTyExpr (TyDep s ty bdy) taken = 
--   getFreeTyExpr ty taken <> getFreeTyExpr bdy (Set.insert s taken)
-- getFreeTyExpr (TyImplDep s ty bdy) taken = 
--   getFreeTyExpr ty taken <> getFreeTyExpr bdy (Set.insert s taken)


-- toTaken - convert an environment to a set containing only its' keys 
toTaken :: Environment -> Set.Set String
toTaken (Environment {localCtx=l, currentModule=(Module m1), globalModule=(Module m2)}) = 
  Set.unions [setOfMap l, setOfMap m1, setOfMap m2]
  where
    setOfMap m = Map.foldrWithKey (\k _ set -> Set.insert (fromString k) set) Set.empty m



t_hasType :: TypeNormal -> TypeNormal -> Bool
t_hasType val ty = 
  case ty of
    NormUniv k -> inUniverse val k
    NormSig fields -> hasFields val fields
    _ -> False

  where
    -- TODO: recursive definitions in type??
    hasFields :: TypeNormal -> [(String, TypeNormal)] -> Bool
    hasFields norm fields = 
      case norm of 
        NormSig fields' -> foldr (\(field, ty) bl ->
                                case getField field fields of 
                                  Just ty' -> t_hasType ty ty' && bl
                                  Nothing -> False) True fields'
        _ -> False

    
    inUniverse :: TypeNormal -> Int -> Bool
    inUniverse norm k =
      case norm of  
        -- TODO: is this correct??
        --   TODO: dependent pair/signature, take max/min??
        NormUniv k' -> k' < k
        _ -> True 
        


getField :: Eq a => a -> [(a, b)] -> Maybe b
getField _ [] = Nothing
getField key ((key', val) : fields) = 
  if key == key' then
    Just val
  else 
    getField key fields


class Expression a where
  free :: a -> Set.Set String
  

instance Expression TypeNormal where 
  free (Neu neutral) = free neutral
  free (NormPrim p) = Set.empty
  free (NormUniv k) = Set.empty
  free (NormDep var a b) =
    Set.union (free a) (Set.delete var (free b))
  free (NormImplDep var a b) =
    Set.union (free a) (Set.delete var (free b))
  free (NormArr a b) =
    Set.union (free a) (free b)
  -- free (NormSig fields) =

instance Expression TypeNeutral where
  free (NeuVar var) = Set.singleton var
  free (NeuApp l r) = Set.union (free l) (free r)
  free (NeuDot sig field) = (free sig)
