module Interpret.Structures.Collections.List (listStructure, listSignature) where

import qualified Data.Map as Map

import qualified Data.Map as Map
import Data
import Interpret.Eval (eval, liftFun, liftFun2, liftFun3, liftFun4, liftFun5)
import Interpret.EvalM
import Interpret.Transform
import Interpret.Structures.BuildStructure

mlsListCtorTy :: Normal
mlsListCtorTy = NormArr (NormUniv 0) (NormUniv 0)

mlsListCtor :: Normal
mlsListCtor = liftFun f mlsListCtorTy
  where f a = pure (CollTy (ListTy a))

consType :: Normal
consType = NormImplProd "A" (NormUniv 0) (NormArr (Neu $ NeuVar "A")
                                          (NormArr (CollTy (ListTy (Neu $ NeuVar "A")))
                                           (CollTy (ListTy (Neu $ NeuVar "A")))))
mlsCons :: Normal
mlsCons = InbuiltCtor $ IndPat "cons" consMatch 1 (liftFun3 consCtor consType) consType
  where
    consMatch :: ([Pattern] -> Normal
                            -> (Normal -> Pattern -> EvalM (Maybe [(String, Normal)]))
                            -> EvalM (Maybe [(String, Normal)]))
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
nilType = NormImplProd "A" (NormUniv 0) (CollTy (ListTy (Neu $ NeuVar ("A"))))

mlsNil :: Normal
mlsNil = InbuiltCtor $ IndPat "nil" nilMatch 1 (liftFun nilCtor nilType) nilType
  where

    nilMatch :: ([Pattern] -> Normal
                           -> (Normal -> Pattern -> EvalM (Maybe [(String, Normal)]))
                           -> EvalM (Maybe [(String, Normal)]))
    nilMatch [] (CollVal (ListVal [] _)) _ = pure $ Just []
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
                (NormArr (NormArr (Neu $ NeuVar "A") (Neu $ NeuVar "B"))
                  (NormArr (CollTy (ListTy (Neu $ NeuVar "A")))
                    (CollTy (ListTy (Neu $ NeuVar "B"))))))

mlsEach :: Normal  
mlsEach = liftFun4 f mlsEachTy
  where f :: Normal -> Normal -> Normal -> Normal -> EvalM Normal
        f _ b func (CollVal (ListVal xs _)) = do
          res <- mapM (\v -> eval (CApp (CNorm func) (CNorm v))) xs
          pure $ CollVal $ ListVal res b

mlsFoldTy :: Normal  
mlsFoldTy = NormImplProd "A" (NormUniv 0)
              (NormImplProd "B" (NormUniv 0)
                (NormArr (NormArr (Neu $ NeuVar "A") (NormArr (Neu $ NeuVar "B") (Neu $ NeuVar "B")))
                  (NormArr (Neu $ NeuVar "B")
                   (NormArr (CollTy (ListTy (Neu $ NeuVar "A"))) (Neu $ NeuVar "B")))))

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
                (NormArr (NormArr (Neu $ NeuVar "A") (NormArr (Neu $ NeuVar "B") (Neu $ NeuVar "B")))
                  (NormArr (Neu $ NeuVar "B")
                   (NormArr (CollTy (ListTy (Neu $ NeuVar "A"))) (Neu $ NeuVar "B")))))

mlsReduce :: Normal  
mlsReduce = liftFun5 f mlsFoldTy
  where f :: Normal -> Normal -> Normal -> Normal -> Normal -> EvalM Normal
        f _ b func z (CollVal (ListVal xs _)) = do
          res <- evalFold func z xs
          pure $ res

        evalFold func z [] = pure z
        evalFold func z (x:xs) = do
          res <- eval (CApp (CApp (CNorm func) (CNorm x)) (CNorm x))
          evalFold func res xs
  
mlsJoinTy :: Normal  
mlsJoinTy = NormImplProd "A" (NormUniv 0)
             (NormArr (CollTy (ListTy (CollTy (ListTy (Neu $ NeuVar "A")))))
               (CollTy (ListTy (Neu $ NeuVar "A"))))

mlsJoin :: Normal  
mlsJoin = liftFun2 f mlsJoinTy
  where f :: Normal -> Normal -> EvalM Normal
        f a (CollVal (ListVal xs _)) = do
          pure $ CollVal $ ListVal (join xs) a

        join :: [Normal] -> [Normal]
        join [] = []
        join ((CollVal (ListVal ys _)) : xs) = ys <> join xs

  
mlsCatTy :: Normal  
mlsCatTy = NormImplProd "A" (NormUniv 0)
             (NormArr (CollTy (ListTy (Neu $ NeuVar "A")))
               (NormArr (CollTy (ListTy (Neu $ NeuVar "A")))
                 (CollTy (ListTy (Neu $ NeuVar "A")))))

mlsCat :: Normal  
mlsCat = liftFun3 f mlsCatTy
  where f :: Normal -> Normal -> Normal -> EvalM Normal
        f a (CollVal (ListVal xs _)) (CollVal (ListVal ys _)) = do
          pure $ CollVal $ ListVal (xs <> ys) a


mlsTakeTy :: Normal  
mlsTakeTy = NormImplProd "A" (NormUniv 0)
             (NormArr (PrimType IntT)
               (NormArr (CollTy (ListTy (Neu $ NeuVar "A")))
                 (CollTy (ListTy (Neu $ NeuVar "A")))))

mlsTake :: Normal  
mlsTake = liftFun3 f mlsTakeTy
  where f :: Normal -> Normal -> Normal -> EvalM Normal
        f _ (PrimVal (Int n)) (CollVal (ListVal xs a)) = do
          pure $ CollVal $ ListVal (take (fromIntegral n) xs) a
  
mlsDropTy :: Normal  
mlsDropTy = NormImplProd "A" (NormUniv 0)
             (NormArr (PrimType IntT)
               (NormArr (CollTy (ListTy (Neu $ NeuVar "A")))
                 (CollTy (ListTy (Neu $ NeuVar "A")))))

mlsDrop :: Normal  
mlsDrop = liftFun3 f mlsDropTy
  where f :: Normal -> Normal -> Normal -> EvalM Normal
        f _ (PrimVal (Int n)) (CollVal (ListVal xs a)) = do
          pure $ CollVal $ ListVal (drop (fromIntegral n) xs) a


listSignature :: Normal
listSignature = NormSig [
  ("M", mlsListCtorTy),
  ("List", mlsListCtorTy),
  ("nil", nilType),
  ("cons", consType),
  ("Ɩ", mlsIndicesOfTy),

  ("¨", mlsEachTy),
  ("fold", mlsFoldTy),
  ("reduce", mlsReduceTy),
  ("join", mlsJoinTy),
  ("⋅", mlsCatTy),
  ("↑", mlsTakeTy),
  ("↓", mlsDropTy)
  ]
  

listStructure :: Normal
listStructure = NormSct [
  ("M", mlsListCtor),
  ("List", mlsListCtor),
  ("nil", mlsNil),
  ("cons", mlsCons),
  ("Ɩ", mlsIndicesOf),

  -- utility functions
  ("¨", mlsEach),
  ("fold", mlsFold),
  ("reduce", mlsReduce),
  ("join", mlsJoin),
  ("⋅", mlsCat),
  ("↑", mlsTake),
  ("↓", mlsDrop)
  --("fold", mlsFold)
  ] listSignature
