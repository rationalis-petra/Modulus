module Data.Environments where 

import Data (Object(..),
             EvalM,
             Expr,
             ModulusType(..))

import qualified Data.Map as Map


-- EnvVal is the value stored in environments, and used when transforming and
-- type checking, but not executing code. 
data EnvVal 
  -- A value known at compile-time  
  = Val Expr ModulusType
  -- A variable whose type needs to be inferred 
  | Infer Int
  -- A variable whose type is known, but whose value is not
  | Var ModulusType

data CheckEnv = CheckEnv {
  tlocalCtx      :: Map.Map String EnvVal,
  tcurrentModule :: Expr,
  tglobalModule  :: Expr
}

