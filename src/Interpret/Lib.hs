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

import Data (Normal, Normal'(NormSct, NormSig), EvalM, toEmpty)
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
            ("structs", NormSct (toEmpty structs) (NormSig []))]
