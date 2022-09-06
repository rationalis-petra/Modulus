module Interpret.Environment where

import Prelude hiding (lookup)

import Data
import Interpret.Transform
import Syntax.Utils (getField)

import qualified Data.Map as Map


lookup :: String -> Environment -> Maybe Normal
lookup key (Environment {localCtx = lcl,
                         currentModule = curr,
                         globalModule = glbl}) = 
  case Map.lookup key lcl of 
    Just x -> Just x
    Nothing ->
      let (NormMod m) = curr in
      case getField key m of
        Just v -> Just v
        Nothing -> Nothing


insert :: String -> Normal -> Environment -> Environment
insert key val context = context{localCtx = newCtx}
  where
    newCtx = Map.insert key val (localCtx context)

insertAll :: [(String, Normal)] -> Environment -> Environment
insertAll lst context = context{localCtx = newCtx}
  where
    newCtx = foldr (uncurry Map.insert) (localCtx context) lst

insertCurrent :: String -> Normal -> Environment -> Environment
insertCurrent key val context = context {currentModule = newModule}
  where
    (NormMod oldModule) = currentModule context
    newModule = NormMod $ (key, val) : oldModule -- TODO this is DODGY!!

empty :: Environment
empty = Environment {localCtx = Map.empty,
                     currentModule = NormMod [],
                     globalModule = NormMod []}
