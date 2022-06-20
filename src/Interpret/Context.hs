module Interpret.Context where

import Prelude hiding (lookup)

import Data
import Interpret.Transform

import qualified Data.Map as Map


lookup :: String -> Context -> Maybe Expr
lookup key (ValContext {localCtx = lcl,
                        currentModule = curr,
                        globalModule = glbl}) = 
  case Map.lookup key lcl of 
    Just x -> Just x
    Nothing ->
      let (Module m) = curr in
      case Map.lookup key m of 
      Just v -> Just v
      Nothing -> Nothing


insert :: String -> Expr -> Context -> Context
insert key val context = context{localCtx = newCtx}
  where
    newCtx = Map.insert key val (localCtx context)

insertAll :: [(String, Expr)] -> Context -> Context
insertAll lst context = context{localCtx = newCtx}
  where
    newCtx = foldr (uncurry Map.insert) (localCtx context) lst

insertCurrent :: String -> Expr -> Context -> Context
insertCurrent key val context = context{currentModule = newModule}
  where
    (Module oldModule) = currentModule context
    newModule = Module $ Map.insert key val oldModule

empty :: Context
empty = ValContext {localCtx = Map.empty,
                    currentModule = Module Map.empty,
                    globalModule = Module Map.empty}
