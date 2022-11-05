module Interpret.Lib.Foreign.C where

import Foreign.Ptr (FunPtr, Ptr, castPtr)
import Foreign.Storable (peek, poke)
import Foreign.C.Types (CDouble, CInt)
import Foreign.C.String (CString, peekCString, newCString)  
import Foreign.Marshal.Alloc

import Data
import Data.Text (pack, unpack)
import Interpret.Eval (eval, liftFun, liftFun2, liftFun3, liftFun4, liftFun5, liftFun6)
import Syntax.Utils (mkVar)

mkCPtr :: Normal
mkCPtr = liftFun f (NormArr (NormUniv 0) (NormUniv 0))
  where
    f ty = pure . CollTy . CPtrTy $ ty

toCInt :: Normal
toCInt = liftFun f (NormArr (PrimType IntT) (PrimType CIntT))
  where
    f (PrimVal (Int i)) = pure . PrimVal . CInt . fromIntegral $ i

fromCInt :: Normal
fromCInt = liftFun f (NormArr (PrimType CIntT) (PrimType IntT))
  where
    f (PrimVal (CInt i)) = pure . PrimVal . Int . toInteger $ i

toCDouble :: Normal
toCDouble = liftFun f (NormArr (PrimType FloatT) (PrimType CDoubleT))
  where
    f (PrimVal (Float f64)) = pure . PrimVal . CDouble . realToFrac $ f64

fromCDouble :: Normal
fromCDouble = liftFun f (NormArr (PrimType CDoubleT) (PrimType FloatT))
  where
    f (PrimVal (CDouble dbl)) = pure . PrimVal . Float . realToFrac $ dbl


toCString :: Normal
toCString = liftFun f (NormArr (PrimType StringT) (CollTy . IOMonadTy $ (PrimType CStringT)))
  where
    f (PrimVal (String str)) =
      pure . CollVal $ IOAction
        (IOThread ((newCString . unpack $ str) >>= (pure . Pure . PrimVal . CString)))
        (CollTy . IOMonadTy $ PrimType CStringT)

fromCString :: Normal
fromCString = liftFun f (NormArr (PrimType CStringT) (CollTy . IOMonadTy $ (PrimType StringT)))
  where
    f (PrimVal (CString str)) =
      pure . CollVal $ IOAction
        (IOThread
          (do hsStr <-  peekCString str
              pure . Pure $ (PrimVal . String . pack $ hsStr)))
        (CollTy . IOMonadTy $ PrimType StringT)

strRefTy :: Normal
strRefTy = (NormArr (PrimType CStringT)
             (CollTy . IOMonadTy $ CollTy . CPtrTy $ (PrimType CStringT)))
  
strRef :: Normal
strRef = liftFun f strRefTy
  where
    f (PrimVal (CString s)) =
      pure . CollVal $ IOAction
        (IOThread
           (do ptr <- malloc :: IO (Ptr CString)
               poke ptr s
               pure . Pure . CollVal . CPtr $ castPtr ptr))
        (CollTy . IOMonadTy $ PrimType StringT)

csignature :: Normal
csignature = NormSig
  [ ("CInt", NormUniv 0)
  , ("CDouble", NormUniv 0)
  , ("CString", NormUniv 0)
  , ("CPtr", NormArr (NormUniv 0) (NormUniv 0))

  , ("str-ref", NormArr (PrimType CStringT) (CollTy . CPtrTy $ (PrimType CStringT)))

  , ("to-c-int", NormArr (PrimType IntT) (PrimType CIntT))
  , ("from-c-int", NormArr (PrimType IntT) (PrimType CIntT))
  , ("to-c-double", NormArr (PrimType FloatT) (PrimType CDoubleT))
  , ("from-c-double", NormArr (PrimType CDoubleT) (PrimType FloatT))
  , ("to-c-string", NormArr (PrimType StringT) (CollTy . IOMonadTy $ (PrimType CStringT)))
  , ("from-c-string", NormArr (PrimType CStringT) (CollTy . IOMonadTy $ (PrimType StringT)))
  ]

  
cstructure :: Normal
cstructure = NormSct (toEmpty
             [ ("CInt", PrimType CIntT)
             , ("CDouble", PrimType CDoubleT)
             , ("CString", PrimType CStringT)
             , ("CPtr", mkCPtr)

             , ("str-ref", strRef)

             , ("to-c-int", toCInt)
             , ("from-c-int", fromCInt)
             , ("to-c-double", toCDouble)
             , ("from-c-double", fromCDouble)
             , ("to-c-string", toCString)
             , ("from-c-string", fromCString)
             ]) csignature

