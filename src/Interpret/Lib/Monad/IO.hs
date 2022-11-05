module Interpret.Lib.Monad.IO (ioMonadStructure, ioMonadSignature) where

import Debug.Trace

import Data
import Interpret.EvalM (ask, get, put, local, throwError)
import Interpret.Eval (eval, evalToEither, liftFun, liftFun2, liftFun4)

mkVar s = (Neu (NeuVar s (NormUniv 0)) (NormUniv 0))
        
ioPureTy :: Normal
ioPureTy = NormImplProd "A" (NormUniv 0)
             (NormArr (mkVar "A")
               (CollTy (IOMonadTy (mkVar "A"))))

ioPure :: Normal
ioPure = liftFun2 f ioPureTy
  where f :: Normal -> Normal -> EvalM Normal
        f _ v = pure $ CollVal $ IOAction (Pure v) ioPureTy

-- Bind :: {A B} → M A → (A → M B) → M B
ioBindTy :: Normal
ioBindTy = NormImplProd "A" (NormUniv 0)
            (NormImplProd "B" (NormUniv 0)
              (NormArr (CollTy (IOMonadTy (mkVar "A")))
                (NormArr (NormArr (mkVar "A") (CollTy (IOMonadTy (mkVar "B"))))
                 (CollTy (IOMonadTy (mkVar "B"))))))
ioBind :: Normal
ioBind = liftFun4 f ioBindTy
  where f :: Normal -> Normal -> Normal -> Normal -> EvalM Normal
        f a b (CollVal (IOAction action ty)) func = do
          pure $ CollVal $ IOAction
            (Bind action func)
            (CollTy (IOMonadTy b))

-- Seq :: {A B} → M A → M B → M B
ioSeqTy :: Normal
ioSeqTy = NormImplProd "A" (NormUniv 0)
            (NormImplProd "B" (NormUniv 0)
              (NormArr (CollTy (IOMonadTy (mkVar "A")))
                (NormArr (CollTy (IOMonadTy (mkVar "B")))
                  (CollTy (IOMonadTy (mkVar "B"))))))
ioSeq :: Normal
ioSeq = liftFun4 f ioSeqTy
  where f :: Normal -> Normal -> Normal -> Normal -> EvalM Normal
        f a b (CollVal (IOAction action ty)) (CollVal (IOAction action' ty')) =
          pure $ CollVal $ IOAction (Seq action action') ty'

ioTyCtor :: Normal   
ioTyCtor = liftFun f (NormArr (NormUniv 0) (NormUniv 0))
  where f :: Normal -> EvalM Normal
        f ty = pure . CollTy . IOMonadTy $ ty
  
ioMonadSignature :: Normal
ioMonadSignature = NormSig
  [ ("IO", (NormArr (NormUniv 0) (NormUniv 0)))
  , ("pure", ioPureTy)
  , (">>=", ioBindTy)
  , (">>", ioSeqTy)
  ] 

ioMonadStructure :: Normal
ioMonadStructure = NormSct (toEmpty
                   [ ("IO", ioTyCtor)
                   , ("pure", ioPure)
                   , (">>=", ioBind)
                   , (">>", ioSeq)
                   ]) ioMonadSignature
