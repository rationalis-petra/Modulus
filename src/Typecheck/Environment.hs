module Typecheck.Environment where

import qualified Data.Map as Map
-- import qualified Data.Set as Set
import Control.Monad.Except

import Data (Object (Module), Context, ValContext(..), Expr, ModulusType)
import Typecheck.InfType
import Typecheck.TypeUtils

data CheckEnv = CheckEnv {
  tlocalCtx      :: Map.Map String InfType,
  tcurrentModule :: Expr,
  tglobalModule  :: Expr
}

toEnv :: Context -> CheckEnv
toEnv (ValContext {currentModule=curr, globalModule=glbl}) = 
  CheckEnv {tlocalCtx = Map.empty,
            tcurrentModule = curr,
            tglobalModule = glbl}


  
lookup :: String -> CheckEnv -> Except String InfType
lookup key (CheckEnv {tlocalCtx = lcl,
                      tcurrentModule = curr,
                      tglobalModule = glbl}) = 
  case Map.lookup key lcl of 
    Just x -> pure x
    Nothing ->
      let (Module m) = curr in
      case Map.lookup key m of 
        Just v -> toInf <$> typeExpr v    
        Nothing -> throwError ("couldn't lookup " <> key)

insert :: String -> InfType -> CheckEnv -> CheckEnv
insert key val context = context{tlocalCtx = newCtx}
  where
    newCtx = Map.insert key val (tlocalCtx context)

