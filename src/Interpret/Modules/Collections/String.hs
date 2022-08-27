module Interpret.Modules.Collections.String (stringModule) where

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
                                  

stringModule :: Normal
stringModule = NormMod $ [
  ("string", PrimType StringT),
  ("t",      PrimType StringT),
  ("append", mlsConcat),
  ("⋅",       mlsConcat),
  ("!!",     mlsElement),
  ("index",  mlsElement)
  ]
