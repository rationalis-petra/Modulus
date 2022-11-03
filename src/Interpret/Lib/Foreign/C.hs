module Interpret.Lib.Foreign.C where

import Foreign.C.Types (CDouble, CInt)  

import Data
import Interpret.Eval (eval, liftFun, liftFun2, liftFun3, liftFun4, liftFun5, liftFun6)

cIntTy :: Normal
cIntTy = PrimType CIntT

cDoubleTy :: Normal
cDoubleTy = PrimType CDoubleT

toCDouble :: Normal
toCDouble = liftFun f (NormArr (PrimType FloatT) (PrimType CDoubleT))
  where
    f (PrimVal (Float f64)) = pure . PrimVal . CDouble . realToFrac $ f64

fromCDouble :: Normal
fromCDouble = liftFun f (NormArr (PrimType CDoubleT) (PrimType FloatT))
  where
    f (PrimVal (CDouble dbl)) = pure . PrimVal . Float . realToFrac $ dbl

csignature :: Normal
csignature = NormSig
  [ ("CInt", NormUniv 0)
  , ("CDouble", NormUniv 0)
  , ("to-c-double", NormArr (PrimType FloatT) (PrimType CDoubleT))
  , ("from-c-double", NormArr (PrimType CDoubleT) (PrimType FloatT))
  ]

  
cstructure :: Normal
cstructure = NormSct (toEmpty
             [ ("CInt", cIntTy)
             , ("CDouble", cDoubleTy)
             , ("to-c-double", toCDouble)
             , ("from-c-double", fromCDouble)
             ]) csignature

