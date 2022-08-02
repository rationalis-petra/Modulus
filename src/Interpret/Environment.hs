module Interpret.Environment where

import Prelude hiding (lookup)

import Data
import Interpret.Transform

import qualified Data.Map as Map


lookup :: String -> Environment -> Maybe Expr
lookup key (Environment {localCtx = lcl,
                         currentModule = curr,
                         globalModule = glbl}) = 
  case Map.lookup key lcl of 
    Just x -> Just x
    Nothing ->
      let (Module m) = curr in
      case Map.lookup key m of 
      Just v -> Just v
      Nothing -> Nothing


insert :: String -> Expr -> Environment -> Environment
insert key val context = context{localCtx = newCtx}
  where
    newCtx = Map.insert key val (localCtx context)

insertAll :: [(String, Expr)] -> Environment -> Environment
insertAll lst context = context{localCtx = newCtx}
  where
    newCtx = foldr (uncurry Map.insert) (localCtx context) lst

insertCurrent :: String -> Expr -> Environment -> Environment
insertCurrent key val context = context{currentModule = newModule}
  where
    (Module oldModule) = currentModule context
    newModule = Module $ Map.insert key val oldModule

empty :: Environment
empty = Environment {localCtx = Map.empty,
                     currentModule = Module Map.empty,
                     globalModule = Module Map.empty}
