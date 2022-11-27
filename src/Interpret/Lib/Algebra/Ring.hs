module Interpret.Lib.Algebra.Ring where

import Data  

import Interpret.Eval
import Interpret.Lib.LibUtils
import Syntax.Utils hiding (tyTail)


ringTy :: Normal m  
ringTy = NormUniv 0

ring :: Normal m
ring = NormSig 
  [ ("T", NormUniv 0)
  , ("e0", mkVar "T")
  , ("e1", mkVar "T")
  , ("+", NormArr (mkVar "T") (NormArr (mkVar "T") (mkVar "T")))
  , ("-", NormArr (mkVar "T") (NormArr (mkVar "T") (mkVar "T")))
  , ("✕", NormArr (mkVar "T") (NormArr (mkVar "T") (mkVar "T")))
  ]

implAddTy :: Normal m
implAddTy = NormImplProd "r" ring 
             (NormArr gt (NormArr gt gt))
  where gt = Neu (NeuDot (NeuVar "r" ring) "T") ring

implAdd :: Normal m
implAdd =
  NormAbs "r"
  (NormAbs "x"
   (NormAbs "y"
    (Neu (NeuApp (NeuApp (NeuDot (NeuVar "r" ring) "+") (Neu (NeuVar "x" t3) t3)) (Neu (NeuVar "y" t3) t3)) t3)
    t2) t1) t0
  where
    t0 = implAddTy
    t1 = tyTail t0
    t2 = tyTail t1
    t3 = tyTail t2


implSubTy :: Normal m
implSubTy = implAddTy

implSub :: Normal m
implSub =
  NormAbs "r"
  (NormAbs "x"
   (NormAbs "y"
    (Neu (NeuApp (NeuApp (NeuDot (NeuVar "r" ring) "-") (Neu (NeuVar "x" t3) t3)) (Neu (NeuVar "y" t3) t3)) t3)
    t2) t1) t0
  where
    t0 = implSubTy
    t1 = tyTail t0
    t2 = tyTail t1
    t3 = tyTail t2
  
  
implMulTy :: Normal m
implMulTy = implAddTy

implMul :: Normal m
implMul =
  NormAbs "g"
  (NormAbs "x"
   (NormAbs "y"
    (Neu (NeuApp (NeuApp (NeuDot (NeuVar "g" ring) "✕") (Neu (NeuVar "x" t3) t3)) (Neu (NeuVar "y" t3) t3)) t3)
    t2) t1) t0
  where
    t0 = implMulTy
    t1 = tyTail t0
    t2 = tyTail t1
    t3 = tyTail t2


ringSignature :: Normal m
ringSignature = NormSig
  [ ("Ring", ringTy)
  , ("+",    implAddTy)
  , ("✕",    implMulTy)
  ]


ringStructure :: Normal m
ringStructure = NormSct
  [ ("Ring", (ring, []))
  , ("+", (implAdd, [Implicit]))
  , ("✕", (implMul, [Implicit]))
  ] ringSignature
