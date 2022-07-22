{-# LANGUAGE TemplateHaskell #-}
module Typecheck.InfType (InfType(..), InfEffectType(..)) where

import qualified Data.Map as Map
import qualified Data.Set as Set

import Data (EffectType(..),
             PrimType(..))  

data InfType 
  = IMVar (Either String Int)
  | IMArr InfType InfType
  | IMDep InfType String InfType
  | IMImplDep InfType String InfType
  | IMSig (Map.Map String InfType)
  | IMDot InfType String
  --        id  name   params        instance-types           
  | IMNamed Int String [InfType] [[InfType]]
  | IMEffect (Set.Set InfEffectType) InfType
  | IMVector InfType

  -- Non-Recursive Types
  | ITypeN Int
  | IMPrim PrimType
  deriving (Show, Eq, Ord)

data InfEffectType
  = IEffIO
  | ICustomEff Int [InfType]  
  deriving (Show, Eq, Ord)
