{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Interpret.Environment where

import Prelude hiding (lookup)

import qualified Data.Map as Map

import Control.Lens hiding (Context, Refl)
import qualified Control.Monad.Except as Except
import Control.Monad.State (MonadState, put, modify)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Reader (MonadReader)

import Data
  
import Syntax.Utils


getThunk :: MonadState (ProgState m) m => Either (Normal m, Normal m) Thunk -> m (Normal m, Normal m)
getThunk (Left v) = pure v
getThunk (Right thunk) = do
  thunks <- use thunk_map
  case Map.lookup thunk thunks of 
    Just (Left func) -> do
      result <- func
      thunk_map %= Map.insert thunk (Right result) 
      pure result
    Just (Right val) -> pure val


lookup :: (MonadError String m, MonadState (ProgState m) m) => String -> Environment m -> m (Normal m, Normal m)
lookup key (Environment {localCtx = lcl,
                         currentModule = curr,
                         globalModule = glbl}) = 
  case Map.lookup key lcl of 
    Just result -> getThunk result
    Nothing ->
      let (NormSct m ty) = curr in
      case getField key m of 
        Just (v, _) -> ((,) v) <$> typeVal v
        Nothing -> throwError ("couldn't lookup " <> key)


lookupGlbl :: String -> Environment m -> Maybe (Normal m, Normal m)
lookupGlbl key (Environment {localCtx = lcl,
                             currentModule = curr,
                             globalModule = glbl}) =
  let (NormSct m ty) = curr in
  case getField key m of 
    Just (v, _) -> (,) v <$> (case Except.runExcept (typeVal v) of Right val -> Just val; _ -> Nothing)
    Nothing -> Nothing

  
lookupGlblS :: String -> Environment m -> Maybe (Normal m, Normal m)
lookupGlblS key (Environment { localCtx = lcl
                             , currentModule = curr
                             , globalModule = glbl }) =
  case Map.lookup key lcl of 
    Just result -> Nothing
    Nothing ->
      let (NormSct m ty) = curr in
        case getField key m of
          Just (v, _) -> (,) v <$> (case Except.runExcept (typeVal v) of Right val -> Just val; _ -> Nothing)
          Nothing -> Nothing


insert :: String -> Normal m -> Normal m -> Environment m -> Environment m 
insert key val ty environment = environment {localCtx = newCtx}
  where
    newCtx = Map.insert key (Left (val, ty)) (localCtx environment)


insertThunk :: String -> Thunk -> Environment m -> Environment m
insertThunk key thunk environment = environment {localCtx = newCtx}
  where
    newCtx = Map.insert key (Right thunk) (localCtx environment)


insertAll :: [(String, (Normal m, Normal m))] -> Environment m -> Environment m
insertAll lst context = context{localCtx = newCtx}
  where
    newCtx = foldr (uncurry (\k v -> Map.insert k (Left v))) (localCtx context) lst


-- TODO: what sould folding over an environment do if a value is thunk'd/
--       current implementation (ignore) is suboptimal
-- Solutions:
-- + Only fold over the types, which can be strict.
fold :: (Normal m -> a -> a) -> a -> Environment m ->  a
fold f z (Environment { localCtx = lcl
                          , currentModule = curr
                          , globalModule = glbl }) = 
  let (NormSct currentFields _) = curr
      (NormSct globalFields _)  = glbl

      z'   = Map.foldr (\case Left (val, ty) -> f val; Right thunk -> id) z lcl 
      z''  = foldr f z' (map (fst . snd) currentFields)
  in foldr f z'' (map (fst . snd) globalFields)


foldImpl :: (Normal m -> a -> a) -> (Normal m -> Normal m -> a -> a) -> a -> Environment m ->  a
foldImpl f1 f2 z (Environment {localCtx = lcl,
                               currentModule = curr,
                               globalModule = glbl}) = 
  let (NormSct currentFields _) = curr
      (NormSct globalFields _)  = glbl

      f1' (v, mods) = if member Implicit mods then f1 v else id

      z'   = Map.foldr (\case Left nt -> uncurry f2 nt; Right thunk -> id) z lcl
      z''  = foldr f1' z' (map snd currentFields)
  in foldr f1' z'' (map snd globalFields)


empty :: Environment m
empty = Environment { localCtx = Map.empty
                    , currentModule = NormSct [] (NormSig [])
                    , globalModule = NormSct [] (NormSig [])}


member _ [] = False
member x' (x:xs) = if x == x' then True else member x' xs
