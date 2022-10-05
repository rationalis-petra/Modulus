module Interpret.Structures.Common (commonTerms, commonStructure) where


import qualified Data.Map as Map

import Data
import Syntax.Utils
import Interpret.Eval (eval, liftFun, liftFun2, liftFun3, liftFun4, liftFun5)
import Interpret.EvalM (throwError)
import Syntax.Utils (mkVar)
import Interpret.Transform


mlsLeftType :: Normal  
mlsLeftType = NormImplProd "A" (NormUniv 0) 
               (NormImplProd "B" (NormUniv 0)
                (NormArr (mkVar "A") (NormArr (mkVar "B") (mkVar "A"))))
  
mlsLeft :: Normal
mlsLeft = liftFun4 f mlsLeftType
  where f _ _ l _ = pure l

mlsRightType :: Normal  
mlsRightType = NormImplProd "A" (NormUniv 0) 
               (NormImplProd "B" (NormUniv 0)
                (NormArr (mkVar "A") (NormArr (mkVar "B") (mkVar "B"))))

mlsRight :: Normal
mlsRight = liftFun4 f mlsRightType
  where f _ _ _ r = pure r
  
mlsComposeType :: Normal  
mlsComposeType = NormImplProd "A" (NormUniv 0) 
                 (NormImplProd "B" (NormUniv 0)
                  (NormImplProd "C" (NormUniv 0)
                   (NormArr (NormArr (mkVar "A") (mkVar "B"))
                    (NormArr (NormArr (mkVar "B") (mkVar "C"))
                     (NormArr (mkVar "A") (mkVar "C"))))))

mlsCompose :: Normal
mlsCompose = liftFun5 f mlsComposeType
  where f a _ c l r = pure $ liftFun (cmp l r) (NormArr a c)
        cmp f1 f2 arg = eval (CApp (CApp (CNorm f1) (CNorm f2)) (CNorm arg))

mlsFlipType :: Normal  
mlsFlipType = NormImplProd "A" (NormUniv 0) 
               (NormImplProd "B" (NormUniv 0)
                (NormImplProd "C" (NormUniv 0)
                 (NormArr (NormArr (mkVar "A") (NormArr (mkVar "B") (mkVar "C")))
                  (NormArr (mkVar "B") (NormArr (mkVar "A") (mkVar "C"))))))

mlsFlip :: Normal
mlsFlip = liftFun4 f mlsFlipType
  where f a b c fnc = pure $ liftFun2 (newFnc fnc) (newType a b c)
        newFnc f x y = eval $ (CApp (CApp (CNorm f) (CNorm x)) (CNorm y))
        newType a b c = NormArr b (NormArr a c)

  
commonSignature :: Normal
commonSignature = NormSig $
  [("⊣", mlsLeftType)
  ,("⊢", mlsRightType)
  ,("∘", mlsComposeType)
  ]


commonStructure :: Normal
commonStructure = NormSct commonTerms commonSignature

commonTerms :: [(String, Normal)]
commonTerms =
  [("⊣", mlsLeft)
  ,("⊢", mlsRight)
  ,("∘", mlsCompose)
  ]
