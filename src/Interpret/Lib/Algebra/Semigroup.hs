module Interpret.Lib.Algebra.Semigroup (semiGroupSignature, semiGroupStructure) where

import Data  

import Interpret.Eval
import Syntax.Utils hiding (tyTail)


semiGroupTy :: Normal  
semiGroupTy = NormUniv 0

semiGroup :: Normal
semiGroup = NormSig 
  [ ("T", NormUniv 0)
  , ("⋅", NormArr (mkVar "T") (NormArr (mkVar "T") (mkVar "T")))
  ]

implStarTy :: Normal
implStarTy = NormImplProd "g" semiGroup 
             (NormArr gt (NormArr gt gt))
  where gt = Neu (NeuDot (NeuVar "g" semiGroup) "T") semiGroup

implStar :: Normal
implStar =
  NormAbs "g"
  (NormAbs "x"
   (NormAbs "y"
    (Neu (NeuApp (NeuApp (NeuDot (NeuVar "g" semiGroup) "⋅") (Neu (NeuVar "x" t3) t3)) (Neu (NeuVar "y" t3) t3)) t3)
    t2) t1) t0
  where
    t0 = implStarTy
    t1 = tyTail t0
    t2 = tyTail t1
    t3 = tyTail t2


semiGroupSignature :: Normal
semiGroupSignature = NormSig
  [ ("Semigroup", semiGroupTy)
  , ("⋅",         implStarTy)
  ]


semiGroupStructure :: Normal
semiGroupStructure = NormSct
  [ ("Semigroup", (semiGroup, []))
  , ("⋅", (implStar, [Implicit]))
  ] semiGroupSignature

tyTail :: Normal -> Normal
tyTail (NormArr l r) = r
tyTail (NormProd sym a b) = b
tyTail (NormImplProd sym a b) = b
