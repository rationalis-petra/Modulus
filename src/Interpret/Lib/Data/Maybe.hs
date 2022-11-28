{-# LANGUAGE FlexibleContexts #-}
module Interpret.Lib.Data.Maybe (maybeStructure, maybeSignature) where

import qualified Data.Map as Map
import Data.Text as Text
import Control.Monad.Reader (MonadReader)
import Control.Monad.State  (MonadState)
import Control.Monad.Except (MonadError)

import Syntax.Normal
import Syntax.Core
import Interpret.Eval (eval, liftFun, liftFun2, liftFun4)
import Syntax.Utils (mkVar)


mlsMaybeCtorTy :: Normal m
mlsMaybeCtorTy = NormArr (NormUniv 0) (NormUniv 0)


mlsMaybeCtor :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsMaybeCtor = liftFun f mlsMaybeCtorTy
  where f a = pure (CollTy (MaybeTy a))


mlsSomeTy :: Normal m
mlsSomeTy = NormImplProd "A" (NormUniv 0)
             (NormArr (mkVar "A")
               (CollTy (MaybeTy (mkVar "A"))))


mlsSome :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsSome = InbuiltCtor $ IndPat "some" someMatch 1 (liftFun2 someCtor mlsSomeTy) mlsSomeTy
  where
    -- someMatch :: ([Pattern] -> Normal
    --                         -> (Normal -> Pattern -> EvalM (Maybe [(String, (Normal, Normal))]))
    --                         -> EvalM (Maybe [(String, (Normal, Normal))]))
    someMatch [p1] (CollVal (MaybeVal (Just x) ty)) matcher = do
      p1' <- matcher x p1 
      case p1' of 
        (Just b1) -> pure $ Just $ b1
        _ -> pure Nothing
    someMatch _ _ _ = pure Nothing

    someCtor :: Applicative m => Normal m -> Normal m -> m (Normal m)
    someCtor ty val = pure (CollVal (MaybeVal (Just val) ty))


mlsNoneTy :: Normal m
mlsNoneTy = NormImplProd "A" (NormUniv 0) (CollTy (MaybeTy (mkVar "A")))


mlsNone :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsNone = InbuiltCtor $ IndPat "none" noneMatch 1 (liftFun noneCtor mlsNoneTy) mlsNoneTy
  where

    -- noneMatch :: ([Pattern] -> Normal
    --                        -> (Normal -> Pattern -> EvalM (Maybe [(String, (Normal, Normal))]))
    --                        -> EvalM (Maybe [(String, (Normal, Normal))]))
    noneMatch [] (CollVal (MaybeVal Nothing _)) _ = pure $ Just []
    noneMatch _ _ _ = pure Nothing

    noneCtor :: Applicative m => Normal m -> m (Normal m)
    noneCtor ty = pure (CollVal (ListVal [] ty))


mlsMapTy :: Normal m
mlsMapTy = NormImplProd "A" (NormUniv 0)
            (NormImplProd "B" (NormUniv 0)
              (NormArr (NormArr (mkVar "A") (mkVar "B"))
                (NormArr (CollTy . MaybeTy . mkVar $ "A")
                  (CollTy . MaybeTy . mkVar $ "B"))))


mlsMap :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsMap = liftFun4 f mlsMapTy
  where
    f :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m -> Normal m -> Normal m -> Normal m -> m (Normal m)
    f a b f (CollVal (MaybeVal m ty)) =
      case m of 
        Just v ->  CollVal . (flip MaybeVal b) . Just <$> eval (CApp (CNorm f) (CNorm v)) 
        Nothing -> pure (CollVal (MaybeVal m b))


maybeSignature :: Normal m
maybeSignature = NormSig
                 [ ("Maybe", mlsMaybeCtorTy)
                 , ("M", mlsMaybeCtorTy)
                 , ("some", mlsSomeTy)
                 , ("none", mlsNoneTy)
                 , ("map", mlsMapTy)
                 ]
                 
  
maybeStructure :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
maybeStructure = NormSct (toEmpty
  [ ("Maybe", mlsMaybeCtor)
  , ("M", mlsMaybeCtor)
  , ("some", mlsSome)
  , ("none", mlsNone)
  , ("map", mlsMap)
  ]) maybeSignature
