module Syntax.Type where

import Data (ModulusType(..),
             Value(Type),
             EvalM) 
import Interpret.EvalM
import qualified Interpret.Environment as Env


eval :: ModulusType -> EvalM ModulusType
eval (TypeN n) = pure (TypeN n)
eval (MVar v) = do 
  env <- ask
  case Env.lookup v env of
    Just (Type ty) -> pure ty
    Just val -> throwError ("non-type symbol when evaluating type!" <> show val)
