module Interpret.Lib.Abs.Algebra.Semigroup where

import Syntax.Normal  

import Interpret.Eval
import Interpret.Lib.LibUtils
import Syntax.Utils hiding (tyTail)


semigroupTy :: Normal m  
semigroupTy = NormUniv 0

semigroup :: Normal m
semigroup = NormSig 
  [ ("T", NormUniv 0)
  , ("⋅", NormArr (mkVar "T") (NormArr (mkVar "T") (mkVar "T")))
  ]

implStarTy :: Normal m
implStarTy = NormProd "g" Hidden semigroup 
             (NormArr gt (NormArr gt gt))
  where gt = Neu (NeuDot (NeuVar "g" semigroup) "T") semigroup

implStar :: Normal m
implStar =
  NormAbs "g"
  (NormAbs "x"
   (NormAbs "y"
    (Neu (NeuApp (NeuApp (NeuDot (NeuVar "g" semigroup) "⋅") (Neu (NeuVar "x" t3) t3)) (Neu (NeuVar "y" t3) t3)) t3)
    t2) t1) t0
  where
    t0 = implStarTy
    t1 = tyTail t0
    t2 = tyTail t1
    t3 = tyTail t2


semigroupSignature :: Normal m
semigroupSignature = NormSig
  [ ("Semigroup", semigroupTy)
  , ("⋅",         implStarTy)
  ]


semigroupStructure :: Normal m
semigroupStructure = NormSct
  [ ("Semigroup", (semigroup, []))
  , ("⋅", (implStar, [Implicit]))
  ] semigroupSignature
