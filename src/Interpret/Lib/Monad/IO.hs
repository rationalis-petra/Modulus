{-# LANGUAGE FlexibleContexts #-}
module Interpret.Lib.Monad.IO (ioMonadStructure, ioMonadSignature) where

import Control.Monad.Reader (MonadReader, local, ask)
import Control.Monad.State  (MonadState)
import Control.Monad.Except (MonadError, throwError)

import Syntax.Normal
import Interpret.Eval (eval, liftFun, liftFun2, liftFun4, liftFunL4)

mkVar s = (Neu (NeuVar s (NormUniv 0)) (NormUniv 0))

getAction :: MonadError String m => m (Normal m) -> m (IEThread m)
getAction n = n >>= f
  where 
    f (CollVal (IOAction t _)) = pure t
    f _ = throwError "bad argument to bind" 

        
ioPureTy :: Normal m
ioPureTy = NormProd "A" Hidden (NormUniv 0)
             (NormArr (mkVar "A")
               (CollTy (IOMonadTy (mkVar "A"))))


ioPure :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
ioPure = liftFun2 f ioPureTy
  where f :: (Applicative m) => Normal m -> Normal m -> m (Normal m)
        f _ v = pure $ CollVal $ IOAction (Pure . pure $v) ioPureTy

-- Bind :: {A B} → M A → (A → M B) → M B
ioBindTy :: Normal m
ioBindTy = NormProd "A" Hidden (NormUniv 0)
            (NormProd "B" Hidden (NormUniv 0)
              (NormArr (CollTy (IOMonadTy (mkVar "A")))
                (NormArr (NormArr (mkVar "A") (CollTy (IOMonadTy (mkVar "B"))))
                 (CollTy (IOMonadTy (mkVar "B"))))))


ioBind :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
ioBind = liftFunL4 f ioBindTy
  where f :: (MonadReader (Environment m) m, MonadError String m) => m (Normal m) -> m (Normal m) -> m (Normal m) -> m (Normal m) -> m (Normal m)
        f a b monad func = do
          env <- ask
          a' <- a
          b' <- b
          pure $ CollVal $ IOAction
            (Bind (local (const env) $ getAction monad) (local (const env) func))
            (CollTy (IOMonadTy b'))

-- Seq :: {A B} → M A → M B → M B
ioSeqTy :: Normal m
ioSeqTy = NormProd "A" Hidden (NormUniv 0)
            (NormProd "B" Hidden (NormUniv 0)
              (NormArr (CollTy (IOMonadTy (mkVar "A")))
                (NormArr (CollTy (IOMonadTy (mkVar "B")))
                  (CollTy (IOMonadTy (mkVar "B"))))))

  
ioSeq :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
ioSeq = liftFunL4 f ioSeqTy
  where f :: (MonadReader (Environment m) m, MonadError String m) => m (Normal m) -> m (Normal m) -> m (Normal m) -> m (Normal m) -> m (Normal m)
        f a b monad1 monad2 = do
          env <- ask
          a' <- a
          b' <- b
          pure $ CollVal $ IOAction (Seq (local (const env) $ getAction monad1)
                                         (local (const env) $ getAction monad2))
                                    (CollTy (IOMonadTy b'))

ioTyCtor :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
ioTyCtor = liftFun f (NormArr (NormUniv 0) (NormUniv 0))
  where f :: (Applicative m) => Normal m -> m (Normal m)
        f ty = pure . CollTy . IOMonadTy $ ty
  
ioMonadSignature :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
ioMonadSignature = NormSig
  [ ("IO", (NormArr (NormUniv 0) (NormUniv 0)))
  , ("pure", ioPureTy)
  , (">>=", ioBindTy)
  , (">>", ioSeqTy)
  ] 

ioMonadStructure :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
ioMonadStructure = NormSct (toEmpty
                   [ ("IO", ioTyCtor)
                   , ("pure", ioPure)
                   , (">>=", ioBind)
                   , (">>", ioSeq)
                   ]) ioMonadSignature
