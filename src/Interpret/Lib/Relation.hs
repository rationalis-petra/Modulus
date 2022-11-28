module Interpret.Lib.Relation where


import Interpret.Lib.LibUtils
import Syntax.Utils (mkVar)
import Syntax.Normal

equalitySig :: Normal m
equalitySig = NormSig
  [ ("T", NormUniv 0)
  , ("=", NormArr (mkVar "T") (NormArr (mkVar "T") (PrimType BoolT)))
  ]


implEqTy :: Normal m
implEqTy = NormImplProd "e" equalitySig
             (NormArr et (NormArr et (PrimType BoolT)))
  where et = Neu (NeuDot (NeuVar "e" equalitySig) "T") equalitySig

implEq :: Normal m
implEq =
  NormAbs "e" (NormAbs "x" (Neu (NeuApp (NeuDot (NeuVar "e" equalitySig) "=") (Neu (NeuVar "x" t2) t2)) t2) t1) t0
  where
    t0 = implEqTy
    t1 = tyTail t0
    t2 = tyTail t1
