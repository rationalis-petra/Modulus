module Interpret.Structures.Monad.IO (ioMonadStructure, ioMonadSignature) where

import Data
import Interpret.Eval (eval, liftFun2, liftFun4)

mkVar s = (Neu (NeuVar s (NormUniv 0)) (NormUniv 0))

-- Bind :: {A A} → M A → (A → M B) → M B
ioBindTy :: Normal
ioBindTy = NormImplProd "A" (NormUniv 0)
            (NormImplProd "B" (NormUniv 0)
              (NormArr (CollTy (IOMonadTy (mkVar "A")))
                (NormArr (NormArr (mkVar "A") (CollTy (IOMonadTy (mkVar "B"))))
                 (CollTy (IOMonadTy (mkVar "B"))))))
ioBind :: Normal
ioBind = liftFun4 f ioBindTy
  where f :: Normal -> Normal -> Normal -> Normal -> EvalM Normal
        f a b (CollVal (IOAction action ty)) func =
          pure $ CollVal $ IOAction (do
                       evalResult <- action
                       pure $ do
                         result' <- evalResult
                         eval (CApp (CNorm func) (CNorm result')))
            (CollTy (IOMonadTy b))

        
ioPureTy :: Normal
ioPureTy = NormImplProd "A" (NormUniv 0)
             (NormArr (mkVar "A")
               (CollTy (IOMonadTy (mkVar "A"))))

ioPure :: Normal
ioPure = liftFun2 f ioPureTy
  where f :: Normal -> Normal -> EvalM Normal
        f _ v = pure $ CollVal $ IOAction (pure $ pure v) ioPureTy
  
ioMonadSignature :: Normal
ioMonadSignature = NormSig [
  ("pure", ioPureTy),
  (">>=", ioBindTy)] 

ioMonadStructure :: Normal
ioMonadStructure = NormSct (toEmpty
                   [ ("pure", ioPure)
                   , (">>=", ioBind)
                   ]) ioMonadSignature
