module Typecheck.InfContext where

import qualified Data.Map as Map
-- import qualified Data.Set as Set
import Control.Monad.Except

import Data (Value (Module),
             EvalM,
             Environment(..),
             Expr,
             ModulusType)
import Typecheck.InfType
import Typecheck.TypeUtils

data Context = Context {
  tlocalCtx      :: Map.Map String (Either InfType (Value EvalM, InfType)),
  tcurrentModule :: Expr,
  tglobalModule  :: Expr
}

envToCtx :: Environment -> Context
envToCtx (Environment {currentModule=curr, globalModule=glbl}) = 
  Context {tlocalCtx = Map.empty,
           tcurrentModule = curr,
           tglobalModule = glbl}


  
lookup :: String -> Context -> Except String (Either InfType (Value EvalM, InfType))
lookup key (Context {tlocalCtx = lcl,
                     tcurrentModule = curr,
                     tglobalModule = glbl}) = 
  case Map.lookup key lcl of 
    Just x -> pure x
    Nothing ->
      let (Module m) = curr in
      case Map.lookup key m of 
        Just v ->  ((Left. toInf) <$> typeExpr v)
        Nothing -> throwError ("couldn't lookup " <> key)

insert :: String -> InfType -> Context -> Context
insert key val context = context {tlocalCtx = newCtx}
  where
    newCtx = Map.insert key (Left val) (tlocalCtx context)
