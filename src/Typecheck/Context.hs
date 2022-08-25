module Typecheck.Context where

import qualified Data.Map as Map
-- import qualified Data.Set as Set
import Control.Monad.Except

import Data (Value (Module),
             TypeNormal,
             EvalM,
             Environment(..),
             Expr)
import Typecheck.TypeUtils

data Context = Context {
  tlocalCtx      :: Map.Map String (Either TypeNormal (Value EvalM, TypeNormal)),
  tcurrentModule :: Expr,
  tglobalModule  :: Expr
}

envToCtx :: Environment -> Context
envToCtx (Environment {currentModule=curr, globalModule=glbl}) = 
  Context {tlocalCtx = Map.empty,
           tcurrentModule = curr,
           tglobalModule = glbl}

ctxToEnv :: Context -> Environment
ctxToEnv (Context {tlocalCtx=lcl, tcurrentModule = curr, tglobalModule = glbl}) =
  (Environment {localCtx=newLcl, currentModule=curr, globalModule=glbl})
  where
    newLcl = Map.foldrWithKey
               (\key entry m' -> case entry of
                   Left _ -> m'
                   Right (val, _) -> Map.insert key val m')
               Map.empty lcl


  
lookup :: String -> Context -> Except String (Either TypeNormal (Value EvalM, TypeNormal))
lookup key (Context {tlocalCtx = lcl,
                     tcurrentModule = curr,
                     tglobalModule = glbl}) = 
  case Map.lookup key lcl of 
    Just x -> pure x
    Nothing ->
      let (Module m) = curr in
      case Map.lookup key m of 
        Just v ->  (Left  <$> typeVal v)
        Nothing -> throwError ("couldn't lookup " <> key)

insert :: String -> TypeNormal -> Context -> Context
insert key val context = context{tlocalCtx = newCtx}
  where
    newCtx = Map.insert key (Left val) (tlocalCtx context)


insertVal :: String -> Value EvalM -> TypeNormal -> Context -> Context
insertVal key val ty context = context{tlocalCtx = newCtx}
  where
    newCtx = Map.insert key (Right (val, ty)) (tlocalCtx context)
