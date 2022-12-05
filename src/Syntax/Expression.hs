module Syntax.Expression where

import qualified Data.Set as Set

class Expression a where
  free :: a -> Set.Set String
  rename :: String -> String -> a -> a
