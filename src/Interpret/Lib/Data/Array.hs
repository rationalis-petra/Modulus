module Interpret.Lib.Data.Array (arrayStructure, arraySignature) where

import qualified Data.Map as Map
import Data.Vector hiding (mapM)
import qualified Data.Vector as Vec

import Data
import Syntax.Core
import Interpret.EvalM 
import Interpret.Eval (eval)
import Syntax.Utils (mkVar)
import Interpret.Eval ( liftFun
                      , liftFun2
                      , liftFun3
                      , liftFun4
                      , liftFun5)
import qualified Interpret.Environment as Env

mlsArrTy :: Normal
mlsArrTy = NormArr (NormUniv 0) (NormUniv 0)


mlsArr :: Normal
mlsArr = liftFun mkArrTy mlsArrTy
  where
    mkArrTy :: Normal -> EvalM Normal
    mkArrTy ty = pure $ CollTy $ ArrayTy ty

  
-- Constructors
mlsIndicesOfTy :: Normal  
mlsIndicesOfTy = NormArr (PrimType IntT) (CollTy (ArrayTy (PrimType IntT)))


mlsIndicesOf :: Normal  
mlsIndicesOf = liftFun f mlsIndicesOfTy
  where f :: Normal -> EvalM Normal
        f (PrimVal (Int n)) = do
          pure $ CollVal $ ArrayVal (fmap (PrimVal . Int) (fromList [1..n])) (PrimType IntT)

  
mlsConsTy :: Normal  
mlsConsTy = NormImplProd "A" (NormUniv 0)
             (NormArr (mkVar "A")
               (NormArr (CollTy . ArrayTy $ mkVar "A")
                 (CollTy . ArrayTy $ mkVar "A")))


mlsCons :: Normal  
mlsCons = liftFun3 f mlsConsTy
  where f :: Normal -> Normal -> Normal -> EvalM Normal
        f a val (CollVal (ArrayVal xs _)) = do
          pure $ CollVal $ ArrayVal (Vec.cons val xs) a

mlsSnocTy :: Normal  
mlsSnocTy = NormImplProd "A" (NormUniv 0)
             (NormArr (mkVar "A")
               (NormArr (CollTy . ArrayTy $ mkVar "A")
                 (CollTy . ArrayTy $ mkVar "A")))


mlsSnoc :: Normal  
mlsSnoc = liftFun3 f mlsSnocTy
  where f :: Normal -> Normal -> Normal -> EvalM Normal
        f a val (CollVal (ArrayVal xs _)) = do
          pure $ CollVal $ ArrayVal (Vec.snoc xs val) a
  

-- Array Operations  
mlsEachTy :: Normal  
mlsEachTy = NormImplProd "A" (NormUniv 0)
              (NormImplProd "B" (NormUniv 0)
                (NormArr (NormArr (mkVar "A") (mkVar "B"))
                  (NormArr (CollTy (ArrayTy (mkVar "A")))
                    (CollTy (ArrayTy (mkVar "B"))))))


mlsEach :: Normal  
mlsEach = liftFun4 f mlsEachTy
  where f :: Normal -> Normal -> Normal -> Normal -> EvalM Normal
        f _ b func (CollVal (ArrayVal xs _)) = do
          res <- Vec.mapM (\v -> eval (CApp (CNorm func) (CNorm v))) xs
          pure $ CollVal $ ArrayVal res b

  
mlsFoldTy :: Normal  
mlsFoldTy = NormImplProd "A" (NormUniv 0)
              (NormImplProd "B" (NormUniv 0)
                (NormArr (NormArr (mkVar "A") (NormArr (mkVar "B") (mkVar "B")))
                  (NormArr (mkVar "B")
                   (NormArr (CollTy (ArrayTy (mkVar "A"))) (mkVar "B")))))


mlsFold :: Normal  
mlsFold = liftFun5 f mlsFoldTy
  where f :: Normal -> Normal -> Normal -> Normal -> Normal -> EvalM Normal
        f _ b func z (CollVal (ArrayVal xs _)) =
          Vec.foldr (liftFold func) (pure z) xs

        liftFold :: Normal -> Normal -> EvalM Normal -> EvalM Normal
        liftFold func val accum = do
          accum' <- accum
          eval (CApp (CApp (CNorm func) (CNorm val)) (CNorm accum'))

  
mlsReduceTy :: Normal  
mlsReduceTy = NormImplProd "A" (NormUniv 0)
              (NormImplProd "B" (NormUniv 0)
                (NormArr (NormArr (mkVar "A") (NormArr (mkVar "B") (mkVar "B")))
                  (NormArr (mkVar "B")
                   (NormArr (CollTy (ArrayTy (mkVar "A"))) (mkVar "B")))))

mlsReduce :: Normal  
mlsReduce = liftFun5 f mlsReduceTy
  where f :: Normal -> Normal -> Normal -> Normal -> Normal -> EvalM Normal
        f _ b func z (CollVal (ArrayVal xs _)) =
          Vec.foldl (liftFold func) (pure z) xs

        liftFold :: Normal -> EvalM Normal -> Normal -> EvalM Normal
        liftFold func accum val = do
          accum' <- accum
          eval (CApp (CApp (CNorm func) (CNorm val)) (CNorm accum'))

  
mlsScanTy :: Normal  
mlsScanTy = NormImplProd "A" (NormUniv 0)
             (NormImplProd "B" (NormUniv 0)
               (NormArr (NormArr (mkVar "A") (NormArr (mkVar "B") (mkVar "B")))
                 (NormArr (mkVar "B")
                   (NormArr (CollTy (ArrayTy (mkVar "A"))) (CollTy (ArrayTy (mkVar "B")))))))


mlsScan :: Normal  
mlsScan = liftFun5 f mlsFoldTy
  where f :: Normal -> Normal -> Normal -> Normal -> Normal -> EvalM Normal
        f _ b func z (CollVal (ArrayVal xs _)) = do
          let vec = Vec.tail $ Vec.scanl (liftScan func) (pure z) xs 
          res' <- unfoldrM extract vec
          pure $ CollVal $ ArrayVal res' b

        liftScan :: Normal -> EvalM Normal -> Normal -> EvalM Normal
        liftScan func accum val = do
          accum' <- accum
          eval (CApp (CApp (CNorm func) (CNorm accum')) (CNorm val))

        extract :: Vector (EvalM Normal) -> EvalM (Maybe (Normal, Vector (EvalM Normal)))
        extract vec = case uncons vec of
          Just (mnd, tail) -> fmap (\val -> Just (val, tail)) mnd
          Nothing -> pure Nothing

   
mlsCatTy :: Normal  
mlsCatTy = NormImplProd "A" (NormUniv 0)
             (NormArr (CollTy (ArrayTy (mkVar "A")))
               (NormArr (CollTy (ArrayTy (mkVar "A")))
                 (CollTy (ArrayTy (mkVar "A")))))


mlsCat :: Normal  
mlsCat = liftFun3 f mlsCatTy
  where f :: Normal -> Normal -> Normal -> EvalM Normal
        f a (CollVal (ArrayVal xs _)) (CollVal (ArrayVal ys _)) = do
          pure $ CollVal $ ArrayVal (xs <> ys) a
  


arraySignature :: Normal
arraySignature = NormSig
                 [ ("Array", mlsArrTy)
                 , ("Ɩ", mlsIndicesOfTy)
                 , ("cons", mlsConsTy)
                 , ("snoc", mlsSnocTy)

                 , ("¨", mlsEachTy)
                 , ("map", mlsEachTy)
                 , ("fold", mlsFoldTy)
                 , ("reduce", mlsReduceTy)
                 , ("/", mlsReduceTy)
                 , ("scan", mlsScanTy)
                 , ("\\", mlsScanTy)
                 , ("⋅", mlsCatTy)
                 ]
                 
                                

arrayStructure :: Normal
arrayStructure = NormSct (toEmpty
                 [ ("Array", mlsArr)
                 , ("Ɩ", mlsIndicesOf)
                 , ("cons", mlsCons)
                 , ("snoc", mlsSnoc)

                 , ("¨", mlsEach)
                 , ("map", mlsEach)
                 , ("fold", mlsFold)
                 , ("reduce", mlsReduce)
                 , ("/", mlsReduce)
                 , ("scan", mlsScan)
                 , ("\\", mlsScan)
                 , ("⋅", mlsCat)
                 ]) arraySignature
