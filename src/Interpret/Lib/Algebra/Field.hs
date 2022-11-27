module Interpret.Lib.Algebra.Field where

import Data  

import Interpret.Lib.Algebra.Ring
  ( implAddTy, implAdd
  , implSubTy, implSub
  , implMulTy, implMul ) 
import Interpret.Eval
import Interpret.Lib.LibUtils
import Syntax.Utils hiding (tyTail)



fieldTy :: Normal m
fieldTy = NormUniv 0

field :: Normal m
field = NormSig 
  [ ("T",  NormUniv 0)
  , ("e0", mkVar "T")
  , ("e1", mkVar "T")
  , ("+",  NormArr (mkVar "T") (NormArr (mkVar "T") (mkVar "T")))
  , ("✕",  NormArr (mkVar "T") (NormArr (mkVar "T") (mkVar "T")))
  , ("-",  NormArr (mkVar "T") (NormArr (mkVar "T") (mkVar "T")))
  , ("÷",  NormArr (mkVar "T") (NormArr (mkVar "T") (mkVar "T")))
  ]


implDivTy :: Normal m
implDivTy = implSubTy

implDiv :: Normal m
implDiv =
  NormAbs "f"
  (NormAbs "x"
   (NormAbs "y"
    (Neu (NeuApp (NeuApp (NeuDot (NeuVar "f" field) "÷") (Neu (NeuVar "x" t3) t3)) (Neu (NeuVar "y" t3) t3)) t3)
    t2) t1) t0
  where
    t0 = implDivTy
    t1 = tyTail t0
    t2 = tyTail t1
    t3 = tyTail t2


fieldSignature :: Normal m
fieldSignature = NormSig
  [ ("Field", fieldTy)
  , ("+",     implAddTy)
  , ("✕",     implMulTy)
  , ("-",     implSubTy)
  , ("÷",     implDivTy)
  ]


fieldStructure :: Normal m
fieldStructure = NormSct
  [ ("Field", (field, []))
  , ("+", (implAdd, [Implicit]))
  , ("✕", (implMul, [Implicit]))
  , ("-", (implSub, [Implicit]))
  , ("÷", (implDiv, [Implicit]))
  ] fieldSignature
