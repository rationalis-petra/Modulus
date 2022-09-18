module Interpret.Structures.Collections.Array (arrayStructure, arraySignature) where

import qualified Data.Map as Map
import Data.Vector hiding (mapM)

import Data
import Interpret.EvalM 
import Interpret.Eval (liftFun2,
                       liftFun3)
import qualified Interpret.Environment as Env
import Interpret.Transform


mlsArr :: Normal
mlsArr = liftFun2 mkArrTy (NormArr (NormUniv 0) (NormArr (CollTy (ListTy (PrimType IntT))) (NormUniv 0)))
  where
    mkArrTy :: Normal -> Normal -> EvalM Normal
    mkArrTy ty (CollVal (ListVal dims _)) = do
      dims' <- mapM asInt dims 
      pure $ CollTy $ ArrayTy ty dims'
    mkArrTy _ _ = throwError "Array type expects list of integers as shape"
   
    asInt :: Normal -> EvalM Integer
    asInt (PrimVal (Int n)) = pure n
    asInt _ = throwError "Array type expects list of integers as shape"

  
arraySignature :: Normal
arraySignature = NormSig [
  ("Array", (NormArr (NormUniv 0) (NormArr (CollTy (ListTy (PrimType IntT))) (NormUniv 0))))]
                                

arrayStructure :: Normal
arrayStructure = NormSct [
  ("Array", mlsArr)]
  arrayStructure
  -- -- Types
  -- ("concat",  mlsConcat),
  -- (",", mlsConcat)
  -- ¨, mlsMap
  -- ⊂, mlsEnclose
  -- ⊆, mlsPartition
  -- ]
