module Interpret.Lib.Relation where


import Interpret.Lib.LibUtils
import Syntax.Utils (mkVar)
import Data

equalitySig :: Normal
equalitySig = NormSig
  [ ("T", NormUniv 0)
  , ("=", NormArr (mkVar "T") (NormArr (mkVar "T") (PrimType BoolT)))
  ]


implEqTy :: Normal
implEqTy = NormImplProd "e" equalitySig
             (NormArr et (NormArr et (PrimType BoolT)))
  where et = Neu (NeuDot (NeuVar "e" equalitySig) "T") equalitySig

implEq :: Normal
implEq =
  NormAbs "e" (NormAbs "x" (Neu (NeuApp (NeuDot (NeuVar "e" equalitySig) "=") (Neu (NeuVar "x" t2) t2)) t2) t1) t0
  where
    t0 = implEqTy
    t1 = tyTail t0
    t2 = tyTail t1
