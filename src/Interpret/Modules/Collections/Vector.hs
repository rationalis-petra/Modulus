module Interpret.Modules.Collections.Vector (vectorModule) where

import Control.Monad.Except (throwError, catchError)

import qualified Data.Map as Map
import Data.Vector

import qualified Interpret.Context as Context
import Data
import Interpret.Eval (liftFun3)
import Interpret.Transform


  

fnConcat :: Expr -> Expr -> Expr -> EvalM Expr  
fnConcat _ (Coll (Vector v1)) (Coll (Vector v2)) = pure $ Coll $ Vector (v1 <> v2)
fnConcat _ _ _ = lift $ throwError "concat expects strings as arguments"
mlsConcat = liftFun3 fnConcat (ImplMDep (TypeN 1) "a"
                               (MArr (MVector (MVar "a"))
                                (MArr (MVector (MVar "a")) (MVector (MVar "a")))))

vectorModule :: Expr
vectorModule = Module $ Map.fromList [
  -- Types
  ("concat",  mlsConcat),
  ("⋅", mlsConcat)
  ]
