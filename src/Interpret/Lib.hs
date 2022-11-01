module Interpret.Lib where


import Control.Monad.State (State)

import Syntax.Utils  

import Interpret.Lib.Core 
import Interpret.Lib.Numerics 
import Interpret.Lib.System 
import Interpret.Lib.Data
import Interpret.Lib.Structures
import Interpret.Lib.Monad 
import Interpret.Lib.Common 
import Interpret.Lib.Algebra 
import Interpret.Lib.Foreign 

import qualified Interpret.Lib.Algebra.Semigroup as Semigroup
import qualified Interpret.Lib.Algebra.Ring as Ring
import qualified Interpret.Lib.Data.String as String

import Data (Normal, Normal'(NormSct, NormSig), EvalM, toEmpty)
import qualified Data.Map as Map


  

implTerms =
  [ ("⋅", Semigroup.implStar)
  , ("+", Ring.implAdd)
  , ("✕", Ring.implMul)
  , ("show", String.implShow)
  ]
  where pathLookup :: [String] -> Normal -> Normal
        pathLookup [] v = v
        pathLookup (s : ss) (NormSct lst _) = case getField s lst of 
          Just (v, _) -> pathLookup ss v
  


defaultStructure :: EvalM [(String, Normal)]
defaultStructure = do
  structs <- structStructure 
  pure $ insertLeft
           (coreTerms <> commonTerms <> implTerms)
           [ ("num",     numStructure)
           , ("sys",     systemStructure)
           , ("data",    dataStructure)
           , ("monad",   monadStructure)
           , ("algebra", algebraStructure)
           , ("structs", NormSct (toEmpty structs) (NormSig []))
           , ("foreign", foreignStructure)
           ]
