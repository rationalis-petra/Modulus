module Interpret.Lib.Data.Maybe (maybeStructure, maybeSignature) where

import qualified Data.Map as Map
import Data.Text as Text

import Data
import Interpret.Eval (liftFun, liftFun2)
import Interpret.EvalM (throwError)
import Interpret.Transform
import Syntax.Utils (mkVar)


mlsMaybeCtorTy :: Normal
mlsMaybeCtorTy = NormArr (NormUniv 0) (NormUniv 0)

mlsMaybeCtor :: Normal
mlsMaybeCtor = liftFun f mlsMaybeCtorTy
  where f a = pure (CollTy (MaybeTy a))

mlsSomeTy :: Normal
mlsSomeTy = NormImplProd "A" (NormUniv 0)
             (NormArr (mkVar "A")
               (CollTy (MaybeTy (mkVar "A"))))
mlsSome :: Normal
mlsSome = InbuiltCtor $ IndPat "some" someMatch 1 (liftFun2 someCtor mlsSomeTy) mlsSomeTy
  where
    someMatch :: ([Pattern] -> Normal
                            -> (Normal -> Pattern -> EvalM (Maybe [(String, (Normal, Normal))]))
                            -> EvalM (Maybe [(String, (Normal, Normal))]))
    someMatch [p1] (CollVal (MaybeVal (Just x) ty)) matcher = do
      p1' <- matcher x p1 
      case p1' of 
        (Just b1) -> pure $ Just $ b1
        _ -> pure Nothing
    someMatch _ _ _ = pure Nothing

    someCtor :: Normal -> Normal -> EvalM Normal
    someCtor ty val = pure (CollVal (MaybeVal (Just val) ty))

mlsNoneTy :: Normal
mlsNoneTy = NormImplProd "A" (NormUniv 0) (CollTy (MaybeTy (mkVar "A")))

mlsNone :: Normal
mlsNone = InbuiltCtor $ IndPat "none" noneMatch 1 (liftFun noneCtor mlsNoneTy) mlsNoneTy
  where

    noneMatch :: ([Pattern] -> Normal
                           -> (Normal -> Pattern -> EvalM (Maybe [(String, (Normal, Normal))]))
                           -> EvalM (Maybe [(String, (Normal, Normal))]))
    noneMatch [] (CollVal (MaybeVal Nothing _)) _ = pure $ Just []
    noneMatch _ _ _ = pure Nothing

    noneCtor :: Normal -> EvalM Normal
    noneCtor ty = pure (CollVal (ListVal [] ty))

maybeSignature :: Normal
maybeSignature = NormSig
                 [ ("M", mlsMaybeCtorTy)
                 , ("some", mlsSomeTy)
                 , ("none", mlsNoneTy)
                 ]
                 
  
maybeStructure :: Normal
maybeStructure = NormSct (toEmpty
  [ ("M", mlsMaybeCtor)
  , ("some", mlsSome)
  , ("none", mlsNone)
  ]) maybeSignature
