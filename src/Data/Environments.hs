module Data.Environments where 

import Data (Value(..),
             EvalM,
             Expr,
             ModulusType(..),
             ValContext(..))

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



  -- TODO: is this how we do it??
fromContext :: ValContext -> CheckEnv   
fromContext (ValContext {localCtx=l, currentModule=c, globalModule=g}) = 
  (CheckEnv {tlocalCtx=Map.empty, tcurrentModule=c, tglobalModule=g})
