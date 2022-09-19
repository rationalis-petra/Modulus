module Interpret.Structures.Collections.List (listStructure, listSignature) where

import qualified Data.Map as Map

import qualified Data.Map as Map
import Data
import Interpret.Eval (liftFun, liftFun2, liftFun3, liftFun4)
import Interpret.EvalM
import Interpret.Transform
import Interpret.Structures.BuildStructure


consType = NormImplProd "A" (NormUniv 0) (NormArr (Neu $ NeuVar "A")
                                          (NormArr (CollTy (ListTy (Neu $ NeuVar "A")))
                                           (CollTy (ListTy (Neu $ NeuVar "A")))))
mlsCons :: Normal
mlsCons = InbuiltCtor $ IndPat "cons" consMatch 1 (liftFun3 consCtor consType) consType
  where
    consMatch :: ([Pattern] -> Normal
                            -> (Normal -> Pattern -> EvalM (Maybe [(String, Normal)]))
                            -> EvalM (Maybe [(String, Normal)]))
    consMatch [p1, p2] (CollVal (ListVal (x:xs) ty)) matcher = do
      p1' <- matcher x p1 
      p2' <- matcher (CollVal (ListVal xs ty)) p2 
      case (p1', p2') of 
        (Just b1, Just b2) -> pure $ Just $ b1 <> b2
        _ -> pure Nothing
    consMatch _ _ _ = pure Nothing

    consCtor :: Normal -> Normal -> Normal -> EvalM Normal
    consCtor _ hd (CollVal (ListVal tl ty)) = pure (CollVal (ListVal (hd:tl) ty))
    consCtor _ _ _ = throwError "bad arguments to constructor: cons"
    

nilType = NormImplProd "A" (NormUniv 0) (CollTy (ListTy (Neu $ NeuVar ("A"))))
mlsNil :: Normal
mlsNil = InbuiltCtor $ IndPat "nil" nilMatch 1 (liftFun nilCtor nilType) nilType
  where

    nilMatch :: ([Pattern] -> Normal
                           -> (Normal -> Pattern -> EvalM (Maybe [(String, Normal)]))
                           -> EvalM (Maybe [(String, Normal)]))
    nilMatch [] (CollVal (ListVal [] _)) _ = pure $ Just []
    nilMatch _ _ _ = pure Nothing

    nilCtor :: Normal -> EvalM Normal
    nilCtor ty = pure (CollVal (ListVal [] ty))
    


listSignature :: Normal
listSignature = NormSig [
  ("nil", nilType),
  ("cons", consType)]
  

listStructure :: Normal
listStructure = NormSct [
  ("nil", mlsNil),
  ("cons", mlsCons)] listSignature
