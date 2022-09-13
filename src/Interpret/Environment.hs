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
      let (NormSct m ty) = curr in
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
    -- TODO: insert type into ty
    (NormSct oldFields ty) = currentModule context
    newModule = NormSct ((key, val) : oldFields) ty

empty :: Environment
empty = Environment {localCtx = Map.empty,
                     currentModule = NormSct [] (NormSig []),
                     globalModule = NormSct [] (NormSig [])}
