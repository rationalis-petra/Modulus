module Interpret.Lib.Data.List (listStructure, listSignature) where

import qualified Data.Map as Map

import qualified Data.Map as Map
import Data
import Syntax.Core
import Interpret.Eval (eval, liftFun, liftFun2, liftFun3, liftFun4, liftFun5, liftFun6)
import Interpret.EvalM
import Syntax.Utils (mkVar)

mlsListCtorTy :: Normal
mlsListCtorTy = NormArr (NormUniv 0) (NormUniv 0)

mlsListCtor :: Normal
mlsListCtor = liftFun f mlsListCtorTy
  where f a = pure (CollTy (ListTy a))

consType :: Normal
consType = NormImplProd "A" (NormUniv 0) (NormArr (mkVar "A")
                                          (NormArr (CollTy (ListTy (mkVar "A")))
                                           (CollTy (ListTy (mkVar "A")))))
mlsCons :: Normal
mlsCons = InbuiltCtor $ IndPat "cons" consMatch 1 (liftFun3 consCtor consType) consType
  where
    consMatch :: Monoid m => ([Pattern] -> Normal
                            -> (Normal -> Pattern -> EvalM (Maybe m))
                            -> EvalM (Maybe m))
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
    

nilType :: Normal
nilType = NormImplProd "A" (NormUniv 0) (CollTy (ListTy (mkVar "A")))

mlsNil :: Normal
mlsNil = InbuiltCtor $ IndPat "nil" nilMatch 1 (liftFun nilCtor nilType) nilType
  where

    nilMatch :: Monoid m => ([Pattern] -> Normal
                           -> (Normal -> Pattern -> EvalM (Maybe m))
                           -> EvalM (Maybe m))
    nilMatch [] (CollVal (ListVal [] _)) _ = pure $ Just mempty
    nilMatch _ _ _ = pure Nothing

    nilCtor :: Normal -> EvalM Normal
    nilCtor ty = pure (CollVal (ListVal [] ty))
    

mlsIndicesOfTy :: Normal  
mlsIndicesOfTy = NormArr (PrimType IntT) (CollTy (ListTy (PrimType IntT)))

mlsIndicesOf :: Normal  
mlsIndicesOf = liftFun f mlsIndicesOfTy
  where f :: Normal -> EvalM Normal
        f (PrimVal (Int n)) = do
          pure $ CollVal $ ListVal (map (PrimVal . Int) [1..n]) (PrimType IntT)

mlsEachTy :: Normal  
mlsEachTy = NormImplProd "A" (NormUniv 0)
              (NormImplProd "B" (NormUniv 0)
                (NormArr (NormArr (mkVar "A") (mkVar "B"))
                  (NormArr (CollTy (ListTy (mkVar "A")))
                    (CollTy (ListTy (mkVar "B"))))))

mlsEach :: Normal  
mlsEach = liftFun4 f mlsEachTy
  where f :: Normal -> Normal -> Normal -> Normal -> EvalM Normal
        f _ b func (CollVal (ListVal xs _)) = do
          res <- mapM (\v -> eval (CApp (CNorm func) (CNorm v))) xs
          pure $ CollVal $ ListVal res b

mlsFoldTy :: Normal  
mlsFoldTy = NormImplProd "A" (NormUniv 0)
              (NormImplProd "B" (NormUniv 0)
                (NormArr (NormArr (mkVar "A") (NormArr (mkVar "B") (mkVar "B")))
                  (NormArr (mkVar "B")
                   (NormArr (CollTy (ListTy (mkVar "A"))) (mkVar "B")))))

mlsFold :: Normal  
mlsFold = liftFun5 f mlsFoldTy
  where f :: Normal -> Normal -> Normal -> Normal -> Normal -> EvalM Normal
        f _ b func z (CollVal (ListVal xs _)) = do
          res <- evalFold func z xs
          pure $ res

        evalFold func z [] = pure z
        evalFold func z (x:xs) = do
          tl <- evalFold func z xs 
          eval (CApp (CApp (CNorm func) (CNorm x)) (CNorm tl)) 
           
mlsReduceTy :: Normal  
mlsReduceTy = NormImplProd "A" (NormUniv 0)
              (NormImplProd "B" (NormUniv 0)
                (NormArr (NormArr (mkVar "A") (NormArr (mkVar "B") (mkVar "B")))
                  (NormArr (mkVar "B")
                   (NormArr (CollTy (ListTy (mkVar "A"))) (mkVar "B")))))

mlsReduce :: Normal  
mlsReduce = liftFun5 f mlsFoldTy
  where f :: Normal -> Normal -> Normal -> Normal -> Normal -> EvalM Normal
        f _ b func z (CollVal (ListVal xs _)) = do
          res <- evalFold func z xs
          pure $ res

        evalFold func z [] = pure z
        evalFold func z (x:xs) = do
          res <- eval (CApp (CApp (CNorm func) (CNorm x)) (CNorm z))
          evalFold func res xs
  
mlsScanTy :: Normal  
mlsScanTy = NormImplProd "A" (NormUniv 0)
             (NormImplProd "B" (NormUniv 0)
               (NormArr (NormArr (mkVar "A") (NormArr (mkVar "B") (mkVar "B")))
                 (NormArr (mkVar "B")
                   (NormArr (CollTy (ListTy (mkVar "A"))) (CollTy (ListTy (mkVar "B")))))))

mlsScan :: Normal  
mlsScan = liftFun5 f mlsFoldTy
  where f :: Normal -> Normal -> Normal -> Normal -> Normal -> EvalM Normal
        f _ b func z (CollVal (ListVal xs _)) = do
          res <- evalScan func z xs [z]
          pure $ CollVal $ ListVal res b

        evalScan func z [] accum = pure $ reverse accum
        evalScan func z (x:xs) accum = do
          res <- eval (CApp (CApp (CNorm func) (CNorm x)) (CNorm z))
          evalScan func res xs (res : accum)

mlsJoinTy :: Normal  
mlsJoinTy = NormImplProd "A" (NormUniv 0)
             (NormArr (CollTy (ListTy (CollTy (ListTy (mkVar "A")))))
               (CollTy (ListTy (mkVar "A"))))

mlsJoin :: Normal  
mlsJoin = liftFun2 f mlsJoinTy
  where f :: Normal -> Normal -> EvalM Normal
        f a (CollVal (ListVal xs _)) = do
          pure $ CollVal $ ListVal (join xs) a

        join :: [Normal] -> [Normal]
        join [] = []
        join ((CollVal (ListVal ys _)) : xs) = ys <> join xs

mlsZipTy :: Normal  
mlsZipTy = NormImplProd "A" (NormUniv 0)
              (NormImplProd "B" (NormUniv 0)
               (NormImplProd "C" (NormUniv 0)
                (NormArr (NormArr (mkVar "A")
                          (NormArr (mkVar "B")
                           (mkVar "C")))
                 (NormArr (CollTy (ListTy (mkVar "A")))
                  (NormArr (CollTy (ListTy (mkVar "B")))
                   (CollTy (ListTy (mkVar "C"))))))))

mlsZip :: Normal
mlsZip =  liftFun6 f mlsZipTy
  where f :: Normal -> Normal -> Normal -> Normal -> Normal -> Normal -> EvalM Normal
        f _ _ c func (CollVal (ListVal xs _)) (CollVal (ListVal ys _)) = do
          res <- join func xs ys
          pure $ CollVal $ ListVal res c

        join :: Normal -> [Normal] -> [Normal] -> EvalM [Normal]
        join func (x:xs) (y:ys) = do
          res <- eval (CApp (CApp (CNorm func) (CNorm x)) (CNorm y))
          tl <- join func xs ys
          pure (res : tl)
        join _ _ _ = pure []

mlsCatTy :: Normal  
mlsCatTy = NormImplProd "A" (NormUniv 0)
             (NormArr (CollTy (ListTy (mkVar "A")))
               (NormArr (CollTy (ListTy (mkVar "A")))
                 (CollTy (ListTy (mkVar "A")))))

mlsCat :: Normal  
mlsCat = liftFun3 f mlsCatTy
  where f :: Normal -> Normal -> Normal -> EvalM Normal
        f a (CollVal (ListVal xs _)) (CollVal (ListVal ys _)) = do
          pure $ CollVal $ ListVal (xs <> ys) a


mlsTakeTy :: Normal  
mlsTakeTy = NormImplProd "A" (NormUniv 0)
             (NormArr (PrimType IntT)
               (NormArr (CollTy (ListTy (mkVar "A")))
                 (CollTy (ListTy (mkVar "A")))))

mlsTake :: Normal  
mlsTake = liftFun3 f mlsTakeTy
  where f :: Normal -> Normal -> Normal -> EvalM Normal
        f _ (PrimVal (Int n)) (CollVal (ListVal xs a)) = do
          pure $ CollVal $ ListVal (take (fromIntegral n) xs) a
  
mlsDropTy :: Normal  
mlsDropTy = NormImplProd "A" (NormUniv 0)
             (NormArr (PrimType IntT)
               (NormArr (CollTy (ListTy (mkVar "A")))
                 (CollTy (ListTy (mkVar "A")))))

mlsDrop :: Normal  
mlsDrop = liftFun3 f mlsDropTy
  where f :: Normal -> Normal -> Normal -> EvalM Normal
        f _ (PrimVal (Int n)) (CollVal (ListVal xs a)) = do
          pure $ CollVal $ ListVal (drop (fromIntegral n) xs) a

mlsReverseTy :: Normal  
mlsReverseTy = NormImplProd "A" (NormUniv 0)
                (NormArr (CollTy (ListTy (mkVar "A")))
                  (CollTy (ListTy (mkVar "A"))))

mlsReverse :: Normal  
mlsReverse = liftFun2 f mlsReverseTy
  where f :: Normal -> Normal -> EvalM Normal
        f a (CollVal (ListVal xs _)) = do
          pure $ CollVal $ ListVal (reverse xs) a

mlsLenTy :: Normal  
mlsLenTy = NormImplProd "A" (NormUniv 0)
                (NormArr (CollTy (ListTy (mkVar "A")))
                  (PrimType IntT))

mlsLen :: Normal  
mlsLen = liftFun2 f mlsLenTy
  where f :: Normal -> Normal -> EvalM Normal
        f _ (CollVal (ListVal xs _)) = do
          pure $ PrimVal $ Int (fromIntegral (length xs))

listSignature :: Normal
listSignature = NormSig 
  [ ("M", mlsListCtorTy)
  , ("List", mlsListCtorTy)
  , ("nil", nilType)
  , ("cons", consType)
  , ("Ɩ", mlsIndicesOfTy)
   
  , ("¨", mlsEachTy)
  , ("map", mlsEachTy)
  , ("fold", mlsFoldTy)
  , ("reduce", mlsReduceTy)
  , ("/", mlsReduceTy)
  , ("scan", mlsScanTy)
  , ("\\", mlsScanTy)
  , ("join", mlsJoinTy)
  , ("zip", mlsZipTy)
  , ("⋅", mlsCatTy)
  , ("↑", mlsTakeTy)
  , ("↓", mlsDropTy)
  , ("reverse", mlsReverseTy)
  , ("ρ", mlsLenTy)
  ]
  

listStructure :: Normal
listStructure = NormSct (toEmpty 
  [ ("M", mlsListCtor)
  , ("List", mlsListCtor)
  , ("nil", mlsNil)
  , ("cons", mlsCons)
  , ("Ɩ", mlsIndicesOf)
 
    -- utility functions
  , ("¨", mlsEach)
  , ("map", mlsEach)
  , ("fold", mlsFold)
  , ("reduce", mlsReduce)
  , ("/", mlsReduce)
  , ("scan", mlsScan)
  , ("\\", mlsScan)
  , ("join", mlsJoin)
  , ("zip", mlsZip)
  , ("⋅", mlsCat)
  , ("↑", mlsTake)
  , ("↓", mlsDrop)
  , ("reverse", mlsReverse)
  , ("ρ", mlsLen)
  ]) listSignature
