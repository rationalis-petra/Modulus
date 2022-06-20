{-# LANGUAGE TemplateHaskell #-}
module Typecheck.Types where


import Control.Lens

import Data (PrimType(..), ModulusType(..))
import qualified Data.Map as Map


data SimpleType
  = SPrimitive PrimType
  | SFunction SimpleType SimpleType
  | SVariable Int
  | SType
  | SModule [(String, SimpleType)]
  deriving (Eq, Show, Ord)

data SmallType
  = SVar Int
  | SMod [(String, SmallType)]
  | SFun SmallType SmallType
  | SImpl [SmallType] SmallType -- implicits are functions
  | SPrim PrimType

data LargeType
  = LType 
  | LSmall SmallType
  | LVar Int
  | LMod [(String, LargeType)]
  | LFun LargeType LargeType

data VarState = VarState
  { _lvl :: Int,
    _upper_bounds :: [SimpleType],
    _lower_bounds :: [SimpleType] }

data TypeCheckState = TypeCheckState {
  _variables :: Map.Map Int VarState,
  _uid_counter :: Int
  }



-- Variable :: looks up a variable in a context
-- lists of upper and lower bounds 

  

$(makeLenses ''VarState)
$(makeLenses ''TypeCheckState)
