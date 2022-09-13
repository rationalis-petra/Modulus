module Interpret.Structures.Collections.String (stringStructure, stringSignature) where

import Control.Monad.Except (throwError, catchError)

import qualified Data.Map as Map
import Data.Text as Text

import Data
import Interpret.Eval (liftFun, liftFun2)
import Interpret.Transform


  

fnConcat :: Normal -> Normal -> EvalM Normal  
fnConcat (PrimVal (String s1)) (PrimVal (String s2)) =
  pure $ PrimVal $ String (s1 <> s2)
fnConcat _ _ = lift $ throwError "append expects strings as arguments"
mlsConcat = liftFun2 fnConcat (NormArr (PrimType StringT)
                               (NormArr (PrimType StringT) (PrimType StringT)))

mlsElement :: Normal
mlsElement = liftFun2 element (NormArr (PrimType StringT)
                               (NormArr (PrimType IntT) (PrimType CharT)))
  where
    element :: Normal -> Normal -> EvalM Normal  
    element (PrimVal (String s)) (PrimVal (Int i)) =
      pure $ PrimVal $ Char (index s (fromEnum i))
    element _ _ = lift $ throwError "element expects string/idx as arguments"
    

mlsLength :: Normal
mlsLength = liftFun len (NormArr (PrimType StringT) (PrimType IntT))
  where
    len :: Normal -> EvalM Normal  
    len (PrimVal (String s)) =
      pure $ PrimVal $ Int (toInteger (Text.length s))
    len _ = lift $ throwError "length expects string as an argument"

strShow :: Normal  
strShow = liftFun sshow (NormArr (PrimType StringT) (PrimType StringT))
  where
    sshow :: Normal -> EvalM Normal
    sshow (PrimVal (String s)) = pure (PrimVal (String s))
    sshow _ = lift $ throwError "length expects string as an argument"
                                  


stringSignature :: Normal  
stringSignature = NormSig [
  ("String",  NormUniv 0),
  ("t",       NormUniv 0),
  ("append",  (NormArr t (NormArr t t))),
  ("⋅",        (NormArr t (NormArr t t))),
  ("show",    (NormArr t (PrimType StringT))),
  ("!!",      (NormArr t (NormArr (PrimType IntT) (NormArr t t)))),
  ("index",   (NormArr t (NormArr (PrimType IntT) (NormArr t t))))]
  where
    t = Neu $ NeuVar "t"

stringStructure :: Normal
stringStructure = NormSct [
  ("String", PrimType StringT),
  ("t",      PrimType StringT),
  ("append", mlsConcat),
  ("⋅",       mlsConcat),
  ("show",   strShow),
  ("!!",     mlsElement),
  ("index",  mlsElement)
  ] stringSignature
