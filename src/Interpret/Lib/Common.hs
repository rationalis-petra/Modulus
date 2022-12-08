{-# LANGUAGE FlexibleContexts #-}
module Interpret.Lib.Common (commonTerms, commonStructure) where


import qualified Data.Map as Map
import Control.Monad.Reader (MonadReader)
import Control.Monad.State  (MonadState)
import Control.Monad.Except (MonadError, throwError)

import Syntax.Normal
import Syntax.Core
import Syntax.Utils
import Interpret.Eval (eval, liftFun, liftFun2, liftFun3, liftFun4, liftFun5, liftFun6)
import Interpret.EvalM
import Interpret.Environment (Environment)
import Syntax.Utils (mkVar)


mlsLeftType :: Normal m
mlsLeftType = NormProd "A" Hidden (NormUniv 0) 
               (NormProd "B" Hidden (NormUniv 0)
                (NormArr (mkVar "A") (NormArr (mkVar "B") (mkVar "A"))))
  
mlsLeft :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsLeft = liftFun4 f mlsLeftType
  where f _ _ l _ = pure l

mlsRightType :: Normal m
mlsRightType = NormProd "A" Hidden (NormUniv 0) 
               (NormProd "B" Hidden (NormUniv 0)
                (NormArr (mkVar "A") (NormArr (mkVar "B") (mkVar "B"))))

mlsRight :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsRight = liftFun4 f mlsRightType
  where f _ _ _ r = pure r
  
mlsComposeType :: Normal m
mlsComposeType = NormProd "A" Hidden (NormUniv 0) 
                 (NormProd "B" Hidden (NormUniv 0)
                  (NormProd "C" Hidden (NormUniv 0)
                   (NormArr (NormArr (mkVar "A") (mkVar "B"))
                    (NormArr (NormArr (mkVar "B") (mkVar "C"))
                     (NormArr (mkVar "A") (mkVar "C"))))))

mlsCompose :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsCompose = liftFun5 f mlsComposeType
  where f a _ c l r = pure $ liftFun (cmp l r) (NormArr a c)
        cmp f1 f2 arg = eval (CApp (CNorm f1) (CApp (CNorm f2) (CNorm arg)))

mlsOverType :: Normal m 
mlsOverType = NormProd "A" Hidden (NormUniv 0) 
                 (NormProd "B" Hidden (NormUniv 0)
                  (NormProd "C" Hidden (NormUniv 0)
                   (NormArr (NormArr (mkVar "B") (NormArr (mkVar "B") (mkVar "C")))
                    (NormArr (NormArr (mkVar "A") (mkVar "B"))
                     (NormArr (mkVar "A") (NormArr (mkVar "A") (mkVar "C")))))))

mlsOver :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsOver = liftFun5 f mlsOverType
  where f a b c l r = pure $ liftFun2 (over l r) (NormArr a (NormArr a c))
        over f g x y = eval (CApp (CApp (CNorm f) (CApp (CNorm g) (CNorm x))) (CApp (CNorm g) (CNorm y)))

mlsFlipType :: Normal m  
mlsFlipType = NormProd "A" Hidden (NormUniv 0) 
               (NormProd "B" Hidden (NormUniv 0)
                (NormProd "C" Hidden (NormUniv 0)
                 (NormArr (NormArr (mkVar "A") (NormArr (mkVar "B") (mkVar "C")))
                  (NormArr (mkVar "B") (NormArr (mkVar "A") (mkVar "C"))))))

mlsFlip :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsFlip = liftFun4 f mlsFlipType
  where f a b c fnc = pure $ liftFun2 (newFnc fnc) (newType a b c)
        newFnc f x y = eval $ (CApp (CApp (CNorm f) (CNorm x)) (CNorm y))
        newType a b c = NormArr b (NormArr a c)

-- before: λ [f g x] (g (f x) x)
-- f : a → b 
-- g : b → a → c
-- x : a
mlsBeforeType :: Normal m
mlsBeforeType = NormProd "A" Hidden (NormUniv 0)
                (NormProd "B" Hidden (NormUniv 0)
                 (NormProd "C" Hidden (NormUniv 0)
                  (NormArr (NormArr (mkVar "A") (mkVar "B"))
                   (NormArr (NormArr (mkVar "B") (NormArr (mkVar "A") (mkVar "C")))
                    (NormArr (mkVar "A") (mkVar "C"))))))

mlsBefore :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsBefore = liftFun5 f mlsBeforeType
  where f a b c f g = pure $ liftFun (newFnc f g) (newType a c)
        newFnc f g x = eval $ (CApp (CApp (CNorm g) (CApp (CNorm f) (CNorm x))) (CNorm x))
        newType a c = NormArr a c 
  
  
-- after: λ [f g x] (f x (g x))
-- f : a → b → c 
-- g : a → b
-- x : a

mlsAfterType :: Normal m
mlsAfterType = NormProd "A" Hidden (NormUniv 0)
                (NormProd "B" Hidden (NormUniv 0)
                 (NormProd "C" Hidden (NormUniv 0)
                  (NormArr (NormArr (mkVar "A") (NormArr (mkVar "B") (mkVar "C")))
                   (NormArr (NormArr (mkVar "A") (mkVar "C"))
                    (NormArr (mkVar "A") (mkVar "C"))))))

mlsAfter :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
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

  
commonSignature :: Normal m
commonSignature = NormSig $
  [ ("⊣", mlsLeftType)
  , ("⊢", mlsRightType)
  , ("∘", mlsComposeType)
  , ("○", mlsOverType)
  , ("⊸", mlsBeforeType)
  , ("⟜", mlsAfterType)
  -- , ("ᛸ", mlsForkType)
  ]


commonStructure :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
commonStructure = NormSct (toEmpty commonTerms) commonSignature

commonTerms :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => [(String, Normal m)]
commonTerms =
  [ ("⊣", mlsLeft)
  , ("⊢", mlsRight)
  , ("∘", mlsCompose)
  , ("○", mlsOver)
  , ("⊸", mlsBefore)
  , ("⟜", mlsAfter)
  -- , ("ᛸ", mlsFork)
  ]
