module Interpret.Modules.Collections.String (stringModule) where

import Control.Monad.Except (throwError, catchError)

import qualified Data.Map as Map
import Data.Text as Text

import Data
import Interpret.Eval (liftFun, liftFun2)
import Interpret.Transform


  

fnConcat :: Expr -> Expr -> EvalM Expr  
fnConcat (PrimE (String s1)) (PrimE (String s2)) =
  pure $ PrimE $ String (s1 <> s2)
fnConcat _ _ = lift $ throwError "append expects strings as arguments"
mlsConcat = liftFun2 fnConcat (NormArr (NormPrim StringT)
                               (NormArr (NormPrim StringT) (NormPrim StringT)))

mlsElement :: Expr
mlsElement = liftFun2 element (NormArr (NormPrim StringT)
                               (NormArr (NormPrim IntT) (NormPrim CharT)))
  where
    element :: Expr -> Expr -> EvalM Expr  
    element (PrimE (String s)) (PrimE (Int i)) =
      pure $ PrimE $ Char (index s (fromEnum i))
    element _ _ = lift $ throwError "element expects string/idx as arguments"
    

mlsLength :: Expr
mlsLength = liftFun len (NormArr (NormPrim StringT) (NormPrim IntT))
  where
    len :: Expr -> EvalM Expr  
    len (PrimE (String s)) =
      pure $ PrimE $ Int (toInteger (Text.length s))
    len _ = lift $ throwError "length expects string as an argument"
                                  

stringModule :: Expr
stringModule = Module $ Map.fromList [
  ("string", Type (NormPrim StringT)),
  ("t",      Type (NormPrim StringT)),
  ("append", mlsConcat),
  ("⋅",       mlsConcat),
  ("!!",     mlsElement),
  ("index",  mlsElement)
  ]
