{-# LANGUAGE FlexibleContexts #-}
module Interpret.Lib where


import qualified Data.Map as Map
import Control.Monad.Reader (MonadReader)
import Control.Monad.State  (MonadState)
import Control.Monad.Except (MonadError)

import Syntax.Normal (Normal(NormSct, NormSig), toEmpty, ProgState)
import Syntax.Utils  
import Interpret.Environment (Environment) 

import Interpret.Lib.Core 
import Interpret.Lib.Numerics 
import Interpret.Lib.System 
import Interpret.Lib.Data
import Interpret.Lib.Monad 
import Interpret.Lib.Common 
import Interpret.Lib.Abs 
import Interpret.Lib.Foreign 

import qualified Interpret.Lib.Abs.Algebra.Semigroup as Semigroup
import qualified Interpret.Lib.Abs.Algebra.Ring as Ring
import qualified Interpret.Lib.Abs.Algebra.Field as Field
import qualified Interpret.Lib.Data.String as String



implTerms =
  [ ("⋅", Semigroup.implStar)
  , ("+", Ring.implAdd)
  , ("✕", Ring.implMul)
  , ("-", Ring.implSub)
  , ("÷", Field.implDiv)
  , ("show", String.implShow)
  ]
  where pathLookup :: [String] -> Normal m -> Normal m
        pathLookup [] v = v
        pathLookup (s : ss) (NormSct lst _) = case getField s lst of 
          Just (v, _) -> pathLookup ss v
  

defaultStructure :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => [(String, Normal m)]
defaultStructure =
  insertLeft (coreTerms <> commonTerms <> implTerms)
           [ ("num",     numStructure)
           , ("sys",     systemStructure)
           , ("data",    dataStructure)
           , ("monad",   monadStructure)
           , ("abs",     absStructure)
           , ("foreign", foreignStructure)
           ]
