module Interpret.Lib.Common (commonTerms, commonStructure) where


import qualified Data.Map as Map

import Data
import Syntax.Utils
import Interpret.Eval (eval, liftFun, liftFun2, liftFun3, liftFun4, liftFun5, liftFun6)
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
        cmp f1 f2 arg = eval (CApp (CNorm f1) (CApp (CNorm f2) (CNorm arg)))

mlsOverType :: Normal  
mlsOverType = NormImplProd "A" (NormUniv 0) 
                 (NormImplProd "B" (NormUniv 0)
                  (NormImplProd "C" (NormUniv 0)
                   (NormArr (NormArr (mkVar "B") (NormArr (mkVar "B") (mkVar "C")))
                    (NormArr (NormArr (mkVar "A") (mkVar "B"))
                     (NormArr (mkVar "A") (NormArr (mkVar "A") (mkVar "C")))))))

mlsOver :: Normal
mlsOver = liftFun5 f mlsOverType
  where f a b c l r = pure $ liftFun2 (over l r) (NormArr a (NormArr a c))
        over f g x y = eval (CApp (CApp (CNorm f) (CApp (CNorm g) (CNorm x))) (CApp (CNorm g) (CNorm y)))

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

-- before: λ [f g x] (g (f x) x)
-- f : a → b 
-- g : b → a → c
-- x : a
mlsBeforeType :: Normal
mlsBeforeType = NormImplProd "A" (NormUniv 0)
                (NormImplProd "B" (NormUniv 0)
                 (NormImplProd "C" (NormUniv 0)
                  (NormArr (NormArr (mkVar "A") (mkVar "B"))
                   (NormArr (NormArr (mkVar "B") (NormArr (mkVar "A") (mkVar "C")))
                    (NormArr (mkVar "A") (mkVar "C"))))))

mlsBefore :: Normal  
mlsBefore = liftFun5 f mlsBeforeType
  where f a b c f g = pure $ liftFun (newFnc f g) (newType a c)
        newFnc f g x = eval $ (CApp (CApp (CNorm g) (CApp (CNorm f) (CNorm x))) (CNorm x))
        newType a c = NormArr a c 
  
  
-- after: λ [f g x] (f x (g x))
-- f : a → b → c 
-- g : a → b
-- x : a

mlsAfterType :: Normal
mlsAfterType = NormImplProd "A" (NormUniv 0)
                (NormImplProd "B" (NormUniv 0)
                 (NormImplProd "C" (NormUniv 0)
                  (NormArr (NormArr (mkVar "A") (NormArr (mkVar "B") (mkVar "C")))
                   (NormArr (NormArr (mkVar "A") (mkVar "C"))
                    (NormArr (mkVar "A") (mkVar "C"))))))

mlsAfter :: Normal  
mlsAfter = liftFun5 f mlsBeforeType
  where f a b c f g = pure $ liftFun (newFnc f g) (newType a c)
        newFnc f g x = eval $ (CApp (CApp (CNorm f) (CNorm x)) (CApp (CNorm g) (CNorm x)))
        newType a c = NormArr a c 
  
-- TODO: fork f g h = λ [x y] f (g x) (h y)
-- f : a → b → c
-- g : d → a
-- h : e → b
-- mlsForkType :: Normal
-- mlsForkType 

-- mlsFork :: Normal

  
commonSignature :: Normal
commonSignature = NormSig $
  [ ("⊣", mlsLeftType)
  , ("⊢", mlsRightType)
  , ("∘", mlsComposeType)
  , ("○", mlsOverType)
  , ("⊸", mlsBeforeType)
  , ("⟜", mlsAfterType)
  -- , ("ᛸ", mlsForkType)
  ]


commonStructure :: Normal
commonStructure = NormSct (toEmpty commonTerms) commonSignature

commonTerms :: [(String, Normal)]
commonTerms =
  [ ("⊣", mlsLeft)
  , ("⊢", mlsRight)
  , ("∘", mlsCompose)
  , ("○", mlsOver)
  , ("⊸", mlsBefore)
  , ("⟜", mlsAfter)
  -- , ("ᛸ", mlsFork)
  ]
