module Interpret.Lib.Algebra.Semigroup where

import Data  

import Interpret.Eval
import Interpret.Lib.LibUtils
import Syntax.Utils hiding (tyTail)


semigroupTy :: Normal  
semigroupTy = NormUniv 0

semigroup :: Normal
semigroup = NormSig 
  [ ("T", NormUniv 0)
  , ("⋅", NormArr (mkVar "T") (NormArr (mkVar "T") (mkVar "T")))
  ]

implStarTy :: Normal
implStarTy = NormImplProd "g" semigroup 
             (NormArr gt (NormArr gt gt))
  where gt = Neu (NeuDot (NeuVar "g" semigroup) "T") semigroup

implStar :: Normal
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


semigroupSignature :: Normal
semigroupSignature = NormSig
  [ ("Semigroup", semigroupTy)
  , ("⋅",         implStarTy)
  ]


semigroupStructure :: Normal
semigroupStructure = NormSct
  [ ("Semigroup", (semigroup, []))
  , ("⋅", (implStar, [Implicit]))
  ] semigroupSignature
