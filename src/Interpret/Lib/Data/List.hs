{-# LANGUAGE FlexibleContexts #-}
module Interpret.Lib.Data.List (listStructure, listSignature) where

import qualified Data.Map as Map
import Control.Monad.Reader (MonadReader)
import Control.Monad.State  (MonadState)
import Control.Monad.Except (MonadError, throwError)

import Syntax.Normal
import Syntax.Core
import Interpret.Eval (eval, liftFun, liftFun2, liftFun3, liftFun4, liftFun5, liftFun6)
import Syntax.Utils (mkVar)

mlsListCtorTy :: Normal m
mlsListCtorTy = NormArr (NormUniv 0) (NormUniv 0)


mlsListCtor :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsListCtor = liftFun f mlsListCtorTy
  where f a = pure (CollTy (ListTy a))


consType :: Normal m
consType = NormImplProd "A" (NormUniv 0) (NormArr (mkVar "A")
                                          (NormArr (CollTy (ListTy (mkVar "A")))
                                           (CollTy (ListTy (mkVar "A")))))

  
mlsCons :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsCons = InbuiltCtor $ IndPat "cons" consMatch 1 (liftFun3 consCtor consType) consType
  where
    -- consMatch :: [Pattern m] -> Normal m
    --                     -> (Normal m -> Pattern m
    --                     -> m (Maybe [(String, (Normal m, Normal m))]))
    --                     -> m (Maybe [(String, (Normal m, Normal m))])
    consMatch [p1, p2] (CollVal (ListVal (x:xs) ty)) matcher = do
      p1' <- matcher x p1 
      p2' <- matcher (CollVal (ListVal xs ty)) p2 
      case (p1', p2') of 
        (Just b1, Just b2) -> pure $ Just $ b1 <> b2
        _ -> pure Nothing
    consMatch _ _ _ = pure Nothing

    consCtor :: MonadError String m => Normal m -> Normal m -> Normal m -> m (Normal m)
    consCtor _ hd (CollVal (ListVal tl ty)) = pure (CollVal (ListVal (hd:tl) ty))
    consCtor _ _ _ = throwError "bad arguments to constructor: cons"
    

nilType :: Normal m
nilType = NormImplProd "A" (NormUniv 0) (CollTy (ListTy (mkVar "A")))


mlsNil :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsNil = InbuiltCtor $ IndPat "nil" nilMatch 1 (liftFun nilCtor nilType) nilType
  where

    -- nilMatch :: Monoid m => ([Pattern] -> Normal
    --                        -> (Normal -> Pattern -> EvalM (Maybe m))
    --                        -> EvalM (Maybe m))
    nilMatch [] (CollVal (ListVal [] _)) _ = pure $ Just mempty
    nilMatch _ _ _ = pure Nothing

    nilCtor :: Applicative m => Normal m -> m (Normal m)
    nilCtor ty = pure (CollVal (ListVal [] ty))
    

mlsIndicesOfTy :: Normal m
mlsIndicesOfTy = NormArr (PrimType IntT) (CollTy (ListTy (PrimType IntT)))


mlsIndicesOf :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsIndicesOf = liftFun f mlsIndicesOfTy
  where f :: Applicative m => Normal m -> m (Normal m)
        f (PrimVal (Int n)) = do
          pure $ CollVal $ ListVal (map (PrimVal . Int) [1..n]) (PrimType IntT)


mlsEachTy :: Normal m
mlsEachTy = NormImplProd "A" (NormUniv 0)
              (NormImplProd "B" (NormUniv 0)
                (NormArr (NormArr (mkVar "A") (mkVar "B"))
                  (NormArr (CollTy (ListTy (mkVar "A")))
                    (CollTy (ListTy (mkVar "B"))))))


mlsEach :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsEach = liftFun4 f mlsEachTy
  where f ::  (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m -> Normal m -> Normal m -> Normal m -> m (Normal m)
        f _ b func (CollVal (ListVal xs _)) = do
          res <- mapM (\v -> eval (CApp (CNorm func) (CNorm v))) xs
          pure $ CollVal $ ListVal res b

  
mlsFoldTy :: Normal m
mlsFoldTy = NormImplProd "A" (NormUniv 0)
              (NormImplProd "B" (NormUniv 0)
                (NormArr (NormArr (mkVar "A") (NormArr (mkVar "B") (mkVar "B")))
                  (NormArr (mkVar "B")
                   (NormArr (CollTy (ListTy (mkVar "A"))) (mkVar "B")))))


mlsFold :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsFold = liftFun5 f mlsFoldTy
  where f :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m -> Normal m -> Normal m -> Normal m -> Normal m -> m (Normal m)
        f _ b func z (CollVal (ListVal xs _)) = do
          res <- evalFold func z xs
          pure $ res

        evalFold func z [] = pure z
        evalFold func z (x:xs) = do
          tl <- evalFold func z xs 
          eval (CApp (CApp (CNorm func) (CNorm x)) (CNorm tl)) 
           

mlsReduceTy :: Normal m
mlsReduceTy = NormImplProd "A" (NormUniv 0)
              (NormImplProd "B" (NormUniv 0)
                (NormArr (NormArr (mkVar "A") (NormArr (mkVar "B") (mkVar "B")))
                  (NormArr (mkVar "B")
                   (NormArr (CollTy (ListTy (mkVar "A"))) (mkVar "B")))))


mlsReduce :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsReduce = liftFun5 f mlsFoldTy
  where f :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m -> Normal m -> Normal m -> Normal m -> Normal m -> m (Normal m)
        f _ b func z (CollVal (ListVal xs _)) = do
          res <- evalFold func z xs
          pure $ res

        evalFold func z [] = pure z
        evalFold func z (x:xs) = do
          res <- eval (CApp (CApp (CNorm func) (CNorm x)) (CNorm z))
          evalFold func res xs
  
mlsScanTy :: Normal m
mlsScanTy = NormImplProd "A" (NormUniv 0)
             (NormImplProd "B" (NormUniv 0)
               (NormArr (NormArr (mkVar "A") (NormArr (mkVar "B") (mkVar "B")))
                 (NormArr (mkVar "B")
                   (NormArr (CollTy (ListTy (mkVar "A"))) (CollTy (ListTy (mkVar "B")))))))


mlsScan :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsScan = liftFun5 f mlsFoldTy
  where f :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m -> Normal m -> Normal m -> Normal m -> Normal m -> m (Normal m)
        f _ b func z (CollVal (ListVal xs _)) = do
          res <- evalScan func z xs [z]
          pure $ CollVal $ ListVal res b

        evalScan func z [] accum = pure $ reverse accum
        evalScan func z (x:xs) accum = do
          res <- eval (CApp (CApp (CNorm func) (CNorm x)) (CNorm z))
          evalScan func res xs (res : accum)


mlsJoinTy :: Normal m
mlsJoinTy = NormImplProd "A" (NormUniv 0)
             (NormArr (CollTy (ListTy (CollTy (ListTy (mkVar "A")))))
               (CollTy (ListTy (mkVar "A"))))


mlsJoin :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsJoin = liftFun2 f mlsJoinTy
  where f :: Applicative m => Normal m -> Normal m -> m (Normal m)
        f a (CollVal (ListVal xs _)) = do
          pure $ CollVal $ ListVal (join xs) a

        join :: [Normal m] -> [Normal m]
        join [] = []
        join ((CollVal (ListVal ys _)) : xs) = ys <> join xs


mlsZipTy :: Normal m
mlsZipTy = NormImplProd "A" (NormUniv 0)
              (NormImplProd "B" (NormUniv 0)
               (NormImplProd "C" (NormUniv 0)
                (NormArr (NormArr (mkVar "A")
                          (NormArr (mkVar "B")
                           (mkVar "C")))
                 (NormArr (CollTy (ListTy (mkVar "A")))
                  (NormArr (CollTy (ListTy (mkVar "B")))
                   (CollTy (ListTy (mkVar "C"))))))))


mlsZip :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsZip =  liftFun6 f mlsZipTy
  where f :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m -> Normal m -> Normal m -> Normal m -> Normal m -> Normal m -> m (Normal m)
        f _ _ c func (CollVal (ListVal xs _)) (CollVal (ListVal ys _)) = do
          res <- join func xs ys
          pure $ CollVal $ ListVal res c

        join :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m -> [Normal m] -> [Normal m] -> m [Normal m]
        join func (x:xs) (y:ys) = do
          res <- eval (CApp (CApp (CNorm func) (CNorm x)) (CNorm y))
          tl <- join func xs ys
          pure (res : tl)
        join _ _ _ = pure []


mlsCatTy :: Normal m
mlsCatTy = NormImplProd "A" (NormUniv 0)
             (NormArr (CollTy (ListTy (mkVar "A")))
               (NormArr (CollTy (ListTy (mkVar "A")))
                 (CollTy (ListTy (mkVar "A")))))


mlsCat :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsCat = liftFun3 f mlsCatTy
  where f :: Applicative m => Normal m -> Normal m -> Normal m -> m (Normal m)
        f a (CollVal (ListVal xs _)) (CollVal (ListVal ys _)) = do
          pure $ CollVal $ ListVal (xs <> ys) a


mlsTakeTy :: Normal m
mlsTakeTy = NormImplProd "A" (NormUniv 0)
             (NormArr (PrimType IntT)
               (NormArr (CollTy (ListTy (mkVar "A")))
                 (CollTy (ListTy (mkVar "A")))))


mlsTake :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsTake = liftFun3 f mlsTakeTy
  where f :: Applicative m => Normal m -> Normal m -> Normal m -> m (Normal m)
        f _ (PrimVal (Int n)) (CollVal (ListVal xs a)) = do
          pure $ CollVal $ ListVal (take (fromIntegral n) xs) a
  

mlsDropTy :: Normal m
mlsDropTy = NormImplProd "A" (NormUniv 0)
             (NormArr (PrimType IntT)
               (NormArr (CollTy (ListTy (mkVar "A")))
                 (CollTy (ListTy (mkVar "A")))))


mlsDrop :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsDrop = liftFun3 f mlsDropTy
  where f :: Applicative m => Normal m -> Normal m -> Normal m -> m (Normal m)
        f _ (PrimVal (Int n)) (CollVal (ListVal xs a)) = do
          pure $ CollVal $ ListVal (drop (fromIntegral n) xs) a


mlsReverseTy :: Normal m
mlsReverseTy = NormImplProd "A" (NormUniv 0)
                (NormArr (CollTy (ListTy (mkVar "A")))
                  (CollTy (ListTy (mkVar "A"))))

mlsReverse :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsReverse = liftFun2 f mlsReverseTy
  where f :: Applicative m => Normal m -> Normal m -> m (Normal m)
        f a (CollVal (ListVal xs _)) = do
          pure $ CollVal $ ListVal (reverse xs) a


mlsLenTy :: Normal m
mlsLenTy = NormImplProd "A" (NormUniv 0)
                (NormArr (CollTy (ListTy (mkVar "A")))
                  (PrimType IntT))


mlsLen :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsLen = liftFun2 f mlsLenTy
  where f :: Applicative m => Normal m -> Normal m -> m (Normal m)
        f _ (CollVal (ListVal xs _)) = do
          pure $ PrimVal $ Int (fromIntegral (length xs))


listSignature :: Normal m
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
  

listStructure :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
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
