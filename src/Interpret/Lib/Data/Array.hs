{-# LANGUAGE FlexibleContexts #-}
module Interpret.Lib.Data.Array (arrayStructure, arraySignature) where

import qualified Data.Map as Map
import qualified Data.Vector as Vec
import Data.Vector hiding (mapM)

import Control.Monad.Reader (MonadReader)
import Control.Monad.State  (MonadState)
import Control.Monad.Except (MonadError, throwError)

import Syntax.Normal
import Syntax.Core
import Interpret.Eval (eval)
import Syntax.Utils (mkVar)
import Interpret.Eval ( liftFun
                      , liftFun2
                      , liftFun3
                      , liftFun4
                      , liftFun5)
import qualified Interpret.Environment as Env
import Interpret.Environment (Environment)

mlsArrTy :: Normal m
mlsArrTy = NormArr (NormUniv 0) (NormUniv 0)


mlsArr :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsArr = liftFun mkArrTy mlsArrTy
  where
    mkArrTy :: Applicative m => Normal m -> m (Normal m)
    mkArrTy ty = pure $ CollTy $ ArrayTy ty

  
-- Constructors
mlsIndicesOfTy :: Normal m
mlsIndicesOfTy = NormArr (PrimType IntT) (CollTy (ArrayTy (PrimType IntT)))


mlsIndicesOf :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsIndicesOf = liftFun f mlsIndicesOfTy
  where f :: Applicative m => Normal m -> m (Normal m)
        f (PrimVal (Int n)) = do
          pure $ CollVal $ ArrayVal (fmap (PrimVal . Int) (fromList [1..n])) (PrimType IntT)


mlsNilTy :: Normal m
mlsNilTy = NormProd "A" Hidden (NormUniv 0)
            (CollTy . ArrayTy $ mkVar "A")


mlsNil :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsNil = liftFun f mlsNilTy
  where f :: Applicative m => Normal m -> m (Normal m)
        f a = pure $ CollVal $ ArrayVal (Vec.empty) a
  

mlsConsTy :: Normal m
mlsConsTy = NormProd "A" Hidden (NormUniv 0)
             (NormArr (mkVar "A")
               (NormArr (CollTy . ArrayTy $ mkVar "A")
                 (CollTy . ArrayTy $ mkVar "A")))


mlsCons :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsCons = liftFun3 f mlsConsTy
  where f :: Applicative m => Normal m -> Normal m -> Normal m -> m (Normal m)
        f a val (CollVal (ArrayVal xs _)) = do
          pure $ CollVal $ ArrayVal (Vec.cons val xs) a

mlsSnocTy :: Normal m
mlsSnocTy = NormProd "A" Hidden (NormUniv 0)
             (NormArr (mkVar "A")
               (NormArr (CollTy . ArrayTy $ mkVar "A")
                 (CollTy . ArrayTy $ mkVar "A")))


mlsSnoc :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsSnoc = liftFun3 f mlsSnocTy
  where f :: Applicative m => Normal m -> Normal m -> Normal m -> m (Normal m)
        f a val (CollVal (ArrayVal xs _)) = do
          pure $ CollVal $ ArrayVal (Vec.snoc xs val) a
  

-- Array Operations  
mlsEachTy :: Normal m
mlsEachTy = NormProd "A" Hidden (NormUniv 0)
              (NormProd "B" Hidden (NormUniv 0)
                (NormArr (NormArr (mkVar "A") (mkVar "B"))
                  (NormArr (CollTy (ArrayTy (mkVar "A")))
                    (CollTy (ArrayTy (mkVar "B"))))))


mlsEach :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsEach = liftFun4 f mlsEachTy
  where f :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m -> Normal m -> Normal m -> Normal m -> m (Normal m)
        f _ b func (CollVal (ArrayVal xs _)) = do
          res <- Vec.mapM (\v -> eval (CApp (CNorm func) (CNorm v))) xs
          pure $ CollVal $ ArrayVal res b

  
mlsFoldTy :: Normal m
mlsFoldTy = NormProd "A" Hidden (NormUniv 0)
              (NormProd "B" Hidden (NormUniv 0)
                (NormArr (NormArr (mkVar "A") (NormArr (mkVar "B") (mkVar "B")))
                  (NormArr (mkVar "B")
                   (NormArr (CollTy (ArrayTy (mkVar "A"))) (mkVar "B")))))


mlsFold :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsFold = liftFun5 f mlsFoldTy
  where f :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m -> Normal m -> Normal m -> Normal m -> Normal m -> m (Normal m)
        f _ b func z (CollVal (ArrayVal xs _)) =
          Vec.foldr (liftFold func) (pure z) xs

        liftFold :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m -> Normal m -> m (Normal m) -> m (Normal m)
        liftFold func val accum = do
          accum' <- accum
          eval (CApp (CApp (CNorm func) (CNorm val)) (CNorm accum'))

  
mlsReduceTy :: Normal m
mlsReduceTy = NormProd "A" Hidden (NormUniv 0)
              (NormProd "B" Hidden (NormUniv 0)
                (NormArr (NormArr (mkVar "A") (NormArr (mkVar "B") (mkVar "B")))
                  (NormArr (mkVar "B")
                   (NormArr (CollTy (ArrayTy (mkVar "A"))) (mkVar "B")))))

mlsReduce :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsReduce = liftFun5 f mlsReduceTy
  where f :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) =>Normal m -> Normal m -> Normal m -> Normal m -> Normal m -> m (Normal m)
        f _ b func z (CollVal (ArrayVal xs _)) =
          Vec.foldl (liftFold func) (pure z) xs

        liftFold :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m -> m (Normal m) -> Normal m -> m (Normal m)
        liftFold func accum val = do
          accum' <- accum
          eval (CApp (CApp (CNorm func) (CNorm val)) (CNorm accum'))

  
mlsScanTy :: Normal m
mlsScanTy = NormProd "A" Hidden (NormUniv 0)
             (NormProd "B" Hidden (NormUniv 0)
               (NormArr (NormArr (mkVar "A") (NormArr (mkVar "B") (mkVar "B")))
                 (NormArr (mkVar "B")
                   (NormArr (CollTy (ArrayTy (mkVar "A"))) (CollTy (ArrayTy (mkVar "B")))))))


mlsScan :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsScan = liftFun5 f mlsFoldTy
  where f :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) =>Normal m -> Normal m -> Normal m -> Normal m -> Normal m -> m (Normal m)
        f _ b func z (CollVal (ArrayVal xs _)) = do
          let vec = Vec.tail $ Vec.scanl (liftScan func) (pure z) xs 
          res' <- unfoldrM extract vec
          pure $ CollVal $ ArrayVal res' b

        liftScan :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m -> m (Normal m) -> Normal m -> m (Normal m)
        liftScan func accum val = do
          accum' <- accum
          eval (CApp (CApp (CNorm func) (CNorm accum')) (CNorm val))

        extract :: Applicative m => Vector (m (Normal m)) -> m (Maybe (Normal m, Vector (m (Normal m))))
        extract vec = case uncons vec of
          Just (mnd, tail) -> fmap (\val -> Just (val, tail)) mnd
          Nothing -> pure Nothing

   
mlsCatTy :: Normal m
mlsCatTy = NormProd "A" Hidden (NormUniv 0)
             (NormArr (CollTy (ArrayTy (mkVar "A")))
               (NormArr (CollTy (ArrayTy (mkVar "A")))
                 (CollTy (ArrayTy (mkVar "A")))))


mlsCat :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsCat = liftFun3 f mlsCatTy
  where f :: Applicative m => Normal m -> Normal m -> Normal m -> m (Normal m)
        f a (CollVal (ArrayVal xs _)) (CollVal (ArrayVal ys _)) = do
          pure $ CollVal $ ArrayVal (xs <> ys) a
  


arraySignature :: Normal m
arraySignature = NormSig
                 [ ("Array", mlsArrTy)
                 , ("Ɩ", mlsIndicesOfTy)
                 , ("cons", mlsConsTy)
                 , ("snoc", mlsSnocTy)
                 , ("nil", mlsNilTy)
                 , ("∅", mlsNilTy)

                 , ("¨", mlsEachTy)
                 , ("map", mlsEachTy)
                 , ("fold", mlsFoldTy)
                 , ("reduce", mlsReduceTy)
                 , ("/", mlsReduceTy)
                 , ("scan", mlsScanTy)
                 , ("\\", mlsScanTy)
                 , ("⋅", mlsCatTy)
                 ]
                 
                                

arrayStructure :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
arrayStructure = NormSct (toEmpty
                 [ ("Array", mlsArr)
                 , ("Ɩ", mlsIndicesOf)
                 , ("cons", mlsCons)
                 , ("snoc", mlsSnoc)
                 , ("nil", mlsNil)
                 , ("∅", mlsNil)

                 , ("¨", mlsEach)
                 , ("map", mlsEach)
                 , ("fold", mlsFold)
                 , ("reduce", mlsReduce)
                 , ("/", mlsReduce)
                 , ("scan", mlsScan)
                 , ("\\", mlsScan)
                 , ("⋅", mlsCat)
                 ]) arraySignature
