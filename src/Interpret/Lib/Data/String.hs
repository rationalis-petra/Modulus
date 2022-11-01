module Interpret.Lib.Data.String where


import qualified Data.Map as Map
import Data.Text as Text

import Data
import Interpret.Lib.LibUtils
import Syntax.Utils (mkVar)
import Interpret.Eval (liftFun, liftFun2)
import Interpret.EvalM (throwError)

  

fnConcat :: Normal -> Normal -> EvalM Normal  
fnConcat (PrimVal (String s1)) (PrimVal (String s2)) =
  pure $ PrimVal $ String (s1 <> s2)
fnConcat _ _ = throwError "append expects strings as arguments"
mlsConcat = liftFun2 fnConcat (NormArr (PrimType StringT)
                               (NormArr (PrimType StringT) (PrimType StringT)))

mlsElement :: Normal
mlsElement = liftFun2 element (NormArr (PrimType StringT)
                               (NormArr (PrimType IntT) (PrimType CharT)))
  where
    element :: Normal -> Normal -> EvalM Normal  
    element (PrimVal (String s)) (PrimVal (Int i)) =
      pure $ PrimVal $ Char (index s (fromEnum i))
    element _ _ = throwError "element expects string/idx as arguments"

mlsLength :: Normal
mlsLength = liftFun len (NormArr (PrimType StringT) (PrimType IntT))
  where
    len :: Normal -> EvalM Normal  
    len (PrimVal (String s)) =
      pure $ PrimVal $ Int (toInteger (Text.length s))
    len _ = throwError "length expects string as an argument"

strShow :: Normal  
strShow = liftFun sshow (NormArr (PrimType StringT) (PrimType StringT))
  where
    sshow :: Normal -> EvalM Normal
    sshow (PrimVal (String s)) = pure (PrimVal (String s))
    sshow _ = throwError "length expects string as an argument"

showableTy :: Normal  
showableTy = NormUniv 0

showable :: Normal
showable = NormSig 
  [ ("T", NormUniv 0)
  , ("show", NormArr (mkVar "T") (PrimType StringT))
  ]

implShowTy :: Normal
implShowTy = NormImplProd "s" showable 
             (NormArr st (PrimType StringT))
  where st = Neu (NeuDot (NeuVar "s" showable) "T") showable

implShow :: Normal
implShow =
  NormAbs "s" (NormAbs "x" (Neu (NeuApp (NeuDot (NeuVar "s" showable) "show") (Neu (NeuVar "x" t2) t2)) t2) t1) t0
  where
    t0 = implShowTy
    t1 = tyTail t0
    t2 = tyTail t1
  
stringSignature :: Normal  
stringSignature = NormSig
                  [ ("String",  NormUniv 0)
                  , ("T",       NormUniv 0)
                  , ("Showable", showableTy)
                  , ("append",  (NormArr t (NormArr t t)))
                  , ("⋅",       (NormArr t (NormArr t t)))
                  , ("show",    (NormArr t (PrimType StringT)))
                  , ("!!",      (NormArr t (NormArr (PrimType IntT) (NormArr t t))))
                  , ("index",   (NormArr t (NormArr (PrimType IntT) (NormArr t t))))
                  ]
  where
    t = Neu (NeuVar "T" (NormUniv 0)) (NormUniv 0)

stringStructure :: Normal
stringStructure = NormSct (toEmpty
                  [ ("String", PrimType StringT)
                  , ("T",      PrimType StringT)
                  , ("Showable", showable)
                  , ("append", mlsConcat)
                  , ("⋅",      mlsConcat)
                  , ("show",   strShow)
                  , ("!!",     mlsElement)
                  , ("index",  mlsElement)
                  ]) stringSignature
