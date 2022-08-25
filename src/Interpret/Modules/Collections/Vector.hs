module Interpret.Modules.Collections.Vector (vectorModule) where

import Control.Monad.Except (throwError, catchError)

import qualified Data.Map as Map
import Data.Vector

import Data
import Interpret.Eval (liftFun3)
import qualified Interpret.Environment as Env
import Interpret.Transform


  

fnConcat :: Expr -> Expr -> Expr -> EvalM Expr  
fnConcat _ (Coll (Vector v1)) (Coll (Vector v2)) = pure $ Coll $ Vector (v1 <> v2)
fnConcat _ _ _ = lift $ throwError "concat expects strings as arguments"
mlsConcat = liftFun3 fnConcat (NormImplDep "a" (NormUniv 0) 
                               (NormArr (NormVector (Neu (NeuVar "a")))
                                (NormArr (NormVector (Neu (NeuVar "a"))) (NormVector (Neu (NeuVar "a"))))))
                                

vectorModule :: Expr
vectorModule = Module $ Map.fromList [
  -- Types
  ("concat",  mlsConcat),
  ("⋅", mlsConcat)
  ]
