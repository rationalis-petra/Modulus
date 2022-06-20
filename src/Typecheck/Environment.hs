module Typecheck.Environment where

import Data (Object (Module), Context, ValContext(..), Expr, ModulusType)
import Data.Environments
import Typecheck.TypeUtils (typeExpr)
import Control.Monad.Except (Except, throwError, catchError, runExcept)
import qualified Data.Map as Map

lookup :: String -> CheckEnv -> Except String EnvVal
lookup key (CheckEnv {tlocalCtx = lcl,
                      tcurrentModule = curr,
                      tglobalModule = glbl}) = 
  case Map.lookup key lcl of 
    Just x -> pure x
    Nothing ->
      let (Module m) = curr in
      case Map.lookup key m of 
        Just v -> Val v <$> typeExpr v    
        Nothing -> throwError ("couldn't lookup " <> key)
  
insert :: String -> EnvVal -> CheckEnv -> CheckEnv
insert key val context = context{tlocalCtx = newCtx}
  where
    newCtx = Map.insert key val (tlocalCtx context)

toCtx :: CheckEnv -> Context
toCtx (CheckEnv {tlocalCtx = lcl,
                 tcurrentModule = curr,
                 tglobalModule = glbl}) = 
  ValContext {localCtx = new_lcl, currentModule = curr, globalModule = glbl}
  where
    new_lcl = Map.foldrWithKey (\k v m -> case v of
                                   Val e _ -> Map.insert k e m
                                   _ -> m) Map.empty lcl

filter :: (EnvVal -> Bool) -> CheckEnv -> Except String CheckEnv
filter f (CheckEnv {tlocalCtx = lcl,
                    tcurrentModule = curr,
                    tglobalModule = glbl}) = do
  let
    (Module cmap) = curr
    (Module gmap) = glbl
    filterExcept f map = 
      (let out = Map.foldrWithKey (\k (v, b) m -> case (runExcept b, m) of
                     (Right bl, Right map) -> Right $ Map.insert k (v, bl) map 
                     (Left err, Right _) -> Left err
                     (_, Left err) -> Left err)
                   (Right Map.empty) (Map.map (\v -> (v, f v)) map)
       in case out of 
         Right map -> pure (Map.map (\(x, _) -> x) (Map.filter (\(_, b) -> b) map))
         Left err -> throwError err)
  newCurr <- filterExcept (\v -> typeExpr v >>= (\t -> pure $ f (Val v t))) cmap
  newGlbl <- filterExcept (\v -> typeExpr v >>= (\t -> pure $ f (Val v t))) gmap

  pure (CheckEnv {tlocalCtx = Map.filter f lcl,
                  tcurrentModule = Module newCurr,
                  tglobalModule = Module newGlbl})


toMap :: CheckEnv -> (Map.Map String EnvVal, Map.Map String Expr)
toMap (CheckEnv {tlocalCtx = lcl,
                 tcurrentModule = curr,
                 tglobalModule = glbl}) = 
  let (Module cmap) = curr
      (Module gmap) = glbl
  in (lcl, (Map.union cmap gmap))


