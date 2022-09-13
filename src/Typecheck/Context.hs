module Typecheck.Context where

import qualified Data.Map as Map
-- import qualified Data.Set as Set
import Control.Monad.Except

import Data (Normal,
             Normal'(NormSct),
             EvalM,
             Environment(..))
import Syntax.Utils

data Context = Context {
  tlocalCtx      :: Map.Map String (Normal, Normal),
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
    newLcl = Map.map (\(val, _) -> val) lcl


  
lookup :: String -> Context -> Except String (Normal, Normal)
lookup key (Context {tlocalCtx = lcl,
                     tcurrentModule = curr,
                     tglobalModule = glbl}) = 
  case Map.lookup key lcl of 
    Just x -> pure x
    Nothing ->
      let (NormSct m ty) = curr in
      case getField key m of 
        Just v -> ((,) v) <$> typeVal v
        Nothing -> throwError ("couldn't lookup " <> key)


insert :: String -> Normal -> Normal -> Context -> Context
insert key val ty context = context{tlocalCtx = newCtx}
  where
    newCtx = Map.insert key (val, ty) (tlocalCtx context)

fold :: (Normal -> a -> a) -> (Normal -> Normal -> a -> a) -> a -> Context ->  a
fold f1 f2 z (Context {tlocalCtx = lcl,
                       tcurrentModule = curr,
                       tglobalModule = glbl}) = 
  let (NormSct tCurrentFields _) = curr
      (NormSct tglobalFields _)  = glbl

      z'   = Map.foldr (uncurry f2) z lcl 
      z''  = foldr f1 z' (map snd tCurrentFields)
  in foldr f1 z'' (map snd tglobalFields)
