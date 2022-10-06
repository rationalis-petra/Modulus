module Interpret.Structures where


import Control.Monad.State (State)

import Syntax.Utils  

import Interpret.Structures.Core 
import Interpret.Structures.Numerics 
import Interpret.Structures.System 
import Interpret.Structures.Data
import Interpret.Structures.Structures
import Interpret.Structures.Monad 
import Interpret.Structures.Common 

import Data (Normal, Normal'(NormSct, NormSig), EvalM)
import qualified Data.Map as Map


defaultStructure :: EvalM [(String, Normal)]
defaultStructure = do
  structs <- structStructure 
  pure $ insertLeft
           (coreTerms <> commonTerms)
           [("num",     numStructure),
            ("sys",     systemStructure),
            ("data",    dataStructure),
            ("monad",   monadStructure),
            ("structs", NormSct structs (NormSig []))]
