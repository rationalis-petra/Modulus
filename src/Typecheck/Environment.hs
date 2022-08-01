module Typecheck.Environment where

import qualified Data.Map as Map
-- import qualified Data.Set as Set
import Control.Monad.Except

import Data (Value (Module), Context, ValContext(..), Expr, ModulusType)
import Typecheck.InfType
import Typecheck.TypeUtils

data CheckEnv m = CheckEnv {
  tlocalCtx      :: Map.Map String (Either InfType (Value m, InfType)),
  tcurrentModule :: Expr,
  tglobalModule  :: Expr
}

toEnv :: Context -> CheckEnv m
toEnv (ValContext {currentModule=curr, globalModule=glbl}) = 
  CheckEnv {tlocalCtx = Map.empty,
            tcurrentModule = curr,
            tglobalModule = glbl}


  
lookup :: String -> CheckEnv m -> Except String (Either InfType (Value m, InfType))
lookup key (CheckEnv {tlocalCtx = lcl,
                      tcurrentModule = curr,
                      tglobalModule = glbl}) = 
  case Map.lookup key lcl of 
    Just x -> pure x
    Nothing ->
      let (Module m) = curr in
      case Map.lookup key m of 
        Just v ->  ((Left. toInf) <$> typeExpr v)
        Nothing -> throwError ("couldn't lookup " <> key)

insert :: String -> InfType -> CheckEnv m -> CheckEnv m
insert key val context = context{tlocalCtx = newCtx}
  where
    newCtx = Map.insert key (Left val) (tlocalCtx context)

