module Interpret.Environment where

import Prelude hiding (lookup)

import qualified Data.Map as Map
import Control.Monad.Except

import Data
import Interpret.Transform
import Syntax.Utils (getField)

import Syntax.Utils



lookup :: String -> Environment -> Except String (Normal, Normal)
lookup key (Environment {localCtx = lcl,
                         currentModule = curr,
                         globalModule = glbl}) = 
  case Map.lookup key lcl of 
    Just x -> pure x
    Nothing ->
      let (NormSct m ty) = curr in
      case getField key m of 
        Just (v, _) -> ((,) v) <$> typeVal v
        Nothing -> throwError ("couldn't lookup " <> key)

lookupMaybe :: String -> Environment -> Maybe (Normal, Normal)
lookupMaybe key (Environment {localCtx = lcl,
                         currentModule = curr,
                         globalModule = glbl}) = 
  case Map.lookup key lcl of 
    Just x -> pure x
    Nothing ->
      let (NormSct m ty) = curr in
      case getField key m of 
        Just (v, _) -> (,) v <$> (case runExcept (typeVal v) of Right val -> Just val; _ -> Nothing)
        Nothing -> Nothing

insert :: String -> Normal -> Normal -> Environment -> Environment
insert key val ty environment = environment {localCtx = newCtx}
  where
    newCtx = Map.insert key (val, ty) (localCtx environment)

insertAll :: [(String, (Normal, Normal))] -> Environment -> Environment
insertAll lst context = context{localCtx = newCtx}
  where
    newCtx = foldr (uncurry Map.insert) (localCtx context) lst

fold :: (Normal -> a -> a) -> a -> Environment ->  a
fold f z (Environment { localCtx = lcl
                          , currentModule = curr
                          , globalModule = glbl }) = 
  let (NormSct currentFields _) = curr
      (NormSct globalFields _)  = glbl

      z'   = Map.foldr f z (Map.map fst lcl) 
      z''  = foldr f z' (map (fst . snd) currentFields)
  in foldr f z'' (map (fst . snd) globalFields)

foldImpl :: (Normal -> a -> a) -> (Normal -> Normal -> a -> a) -> a -> Environment ->  a
foldImpl f1 f2 z (Environment {localCtx = lcl,
                               currentModule = curr,
                               globalModule = glbl}) = 
  let (NormSct currentFields _) = curr
      (NormSct globalFields _)  = glbl

      f1' (v, mods) = if member Implicit mods then f1 v else id

      z'   = Map.foldr (uncurry f2) z lcl 
      z''  = foldr f1' z' (map snd currentFields)
  in foldr f1' z'' (map snd globalFields)

empty :: Environment
empty = Environment { localCtx = Map.empty
                    , currentModule = NormSct [] (NormSig [])
                    , globalModule = NormSct [] (NormSig [])
                    }

member _ [] = False
member x' (x:xs) = if x == x' then True else member x' xs
