module Interpret.Lib.Foreign.C where

import Data


cintTyTy :: Normal
cintTyTy = NormUniv 0
 
cintTy :: Normal
cintTy = PrimType CIntT



csignature :: Normal
csignature = NormSig
  [ ("CInt", cintTyTy)
  ]

  
cstructure :: Normal
cstructure = NormSct (toEmpty
             [ ("CInt", cintTy)
             ]) csignature

