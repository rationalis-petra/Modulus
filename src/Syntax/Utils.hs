{-# LANGUAGE FlexibleContexts #-}

module Syntax.Utils where

import Syntax.Normal
import Control.Monad.Except (MonadError, throwError, catchError)

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

restrict :: Eq a => [(a, b)] -> [(a, c)] -> [(a, (b, c))]
restrict [] sig = []
restrict ((k, v) : tail) sig =
  case getField k sig of 
    Just ty  -> (k, (v, ty)) : restrict tail sig
    Nothing -> restrict tail sig


  

typeVal :: (MonadError String m) => Normal n -> m (Normal n)
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

      CInt _ -> CIntT
      CDouble _ -> CDoubleT
      CString _ -> CStringT
typeVal (Refl ty) = pure $ PropEq ty ty
typeVal (PropEq _ _) = pure $ NormUniv 0
typeVal (InbuiltCtor ctor) = case ctor of 
  IndPat _ _ _ _ ty -> pure ty
typeVal (NormCoVal _ ty) = pure ty
typeVal (NormCoDtor _ _ _ _ _ _ ty) = pure ty

-- type of types
typeVal (NormUniv k) = pure (NormUniv (k + 1))
typeVal (NormIType _ _ _) = pure (NormUniv 0)
typeVal (NormArr _ _) = pure (NormUniv 0)
typeVal (NormProd _ _ _ _) = pure (NormUniv 0)
typeVal (NormSig _) = pure $ NormUniv 0

-- Functions
typeVal (Builtin _ ty) = pure ty
typeVal (NormAbs _ _ ty) = pure ty
typeVal (NormSct m ty) = pure ty

typeVal (NormIVal _ _ _ _ _ ty) = pure ty
typeVal (CollTy _) = pure $ NormUniv 0
typeVal (CollVal val) = case val of
  IOAction _ ty -> pure ty
  ListVal _ ty -> pure (CollTy (ListTy ty))
  ArrayVal _ ty -> pure (CollTy (ArrayTy ty))

typeVal (Neu _ ty) = pure ty
typeVal (Special _) = pure $ PrimType SpecialT
typeVal (NormCModule _) = pure $ PrimType CModuleT
typeVal (NormCValue _ ty) = pure $ ty
typeVal (BuiltinMac _) = pure $ PrimType MacroT -- TODO: add proper macro types!!
typeVal e = throwError $ "untypable value: " <> show e


        




  

-- TODO: should type annotations be included in free???


mkVar s = Neu (NeuVar s (NormUniv 0)) (NormUniv 0)
mkNVar s = NeuVar s (NormUniv 0)

freshen :: Set.Set String -> String -> String
freshen set str = 
  if Set.member str set then
    freshen set ("*" <> str) 
  else
    str

tyModifier :: (MonadError String m) => Normal n -> m ArgType
tyModifier (NormArr _ _) = pure Visible
tyModifier (NormProd _ m _ _) = pure m
tyModifier ty = throwError ("can't get type modifier of " <> show ty)

tyHead :: (MonadError String m) => Normal n -> m (Normal n)
tyHead (NormArr l r) = pure l
tyHead (NormProd sym _ a b) = pure a
tyHead hd = throwError ("can't get type head of " <> show hd)

tyHeadStr :: (MonadError String m) => Normal n -> m (Normal n, String)
tyHeadStr (NormProd sym _ a b) = pure (a, sym)
tyHeadStr hd = throwError ("can't get type head str of " <> show hd)

tyTail :: (MonadError String m) => Normal n -> m (Normal n)
tyTail (NormArr l r) = pure r
tyTail (NormProd sym aty a b) = pure b
tyTail hd = throwError ("can't get type tail of " <> show hd)

tySize :: Normal n -> Int
tySize (NormArr _ r) = 1 + tySize r
tySize (NormProd _ _ _ r) = 1 + tySize r
tySize _ = 0
  

isFncType :: Normal m -> Bool
isFncType (NormArr _ _) = True
isFncType (NormProd _ _ _ _) = True
isFncType _ = False

patVars :: Pattern m -> Set.Set String
patVars WildCard = Set.empty
patVars (VarBind sym _) = Set.singleton sym
patVars (MatchInduct id1 id2 subpats) = foldr Set.union Set.empty (map patVars subpats)
