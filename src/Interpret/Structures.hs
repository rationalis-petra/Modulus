module Interpret.Structures where


import Control.Monad.State (State)

import Syntax.Utils  

import qualified Interpret.Structures.Core as Core
import qualified Interpret.Structures.Numerics as Num
import qualified Interpret.Structures.System as Sys
import Interpret.Structures.Data
import qualified Interpret.Structures.Structures as Sct
import qualified Interpret.Structures.Monad as Mnd

import Data (Normal, Normal'(NormSct, NormSig), EvalM)
import qualified Data.Map as Map

coreStructure    = Core.coreStructure
numStructure     = Num.numStructure
numSignature     = Num.numSignature
systemStructure  = Sys.systemStructure
systemSignature  = Sys.systemSignature

defaultStructure :: EvalM [(String, Normal)]
defaultStructure = do
  structs <- Sct.structStructure 
  pure $ insertLeft coreStructure [("num",     NormSct numStructure numSignature),
                                   ("sys",     NormSct systemStructure systemSignature),
                                   ("data",    dataStructure),
                                   ("monad",   Mnd.monadStructure),
                                   ("structs", NormSct structs (NormSig []))
                                  ]
