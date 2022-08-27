module Typecheck.Context where

import qualified Data.Map as Map
-- import qualified Data.Set as Set
import Control.Monad.Except

import Data (Normal,
             Normal'(NormMod),
             EvalM,
             Environment(..))
import Syntax.Utils

data Context = Context {
  tlocalCtx      :: Map.Map String (Either Normal (Normal, Normal)),
  tcurrentModule :: Normal,
  tglobalModule  :: Normal
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


  
lookup :: String -> Context -> Except String (Either Normal (Normal, Normal))
lookup key (Context {tlocalCtx = lcl,
                     tcurrentModule = curr,
                     tglobalModule = glbl}) = 
  case Map.lookup key lcl of 
    Just x -> pure x
    Nothing ->
      let (NormMod m) = curr in
      case getField key m of 
        Just v -> (Left  <$> typeVal v)
        Nothing -> throwError ("couldn't lookup " <> key)

insert :: String -> Normal -> Context -> Context
insert key val context = context{tlocalCtx = newCtx}
  where
    newCtx = Map.insert key (Left val) (tlocalCtx context)


insertVal :: String -> Normal -> Normal -> Context -> Context
insertVal key val ty context = context{tlocalCtx = newCtx}
  where
    newCtx = Map.insert key (Right (val, ty)) (tlocalCtx context)
