module Interpret.Lib.Data.Maybe (maybeStructure, maybeSignature) where

import qualified Data.Map as Map
import Data.Text as Text

import Data
import Syntax.Core
import Interpret.Eval (eval, liftFun, liftFun2, liftFun4)
import Interpret.EvalM (throwError)
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


mlsMapTy :: Normal  
mlsMapTy = NormImplProd "A" (NormUniv 0)
            (NormImplProd "B" (NormUniv 0)
              (NormArr (NormArr (mkVar "A") (mkVar "B"))
                (NormArr (CollTy . MaybeTy . mkVar $ "A")
                  (CollTy . MaybeTy . mkVar $ "B"))))

mlsMap :: Normal  
mlsMap = liftFun4 f mlsMapTy
  where
    f :: Normal -> Normal -> Normal -> Normal -> EvalM Normal
    f a b f (CollVal (MaybeVal m ty)) =
      case m of 
        Just v ->  CollVal . (flip MaybeVal b) . Just <$> eval (CApp (CNorm f) (CNorm v)) 
        Nothing -> pure (CollVal (MaybeVal m b))

maybeSignature :: Normal
maybeSignature = NormSig
                 [ ("Maybe", mlsMaybeCtorTy)
                 , ("M", mlsMaybeCtorTy)
                 , ("some", mlsSomeTy)
                 , ("none", mlsNoneTy)
                 , ("map", mlsMapTy)
                 ]
                 
  
maybeStructure :: Normal
maybeStructure = NormSct (toEmpty
  [ ("Maybe", mlsMaybeCtor)
  , ("M", mlsMaybeCtor)
  , ("some", mlsSome)
  , ("none", mlsNone)
  , ("map", mlsMap)
  ]) maybeSignature
