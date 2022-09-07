module Interpret.Structures where


import Control.Monad.State (State)

import Syntax.Utils  

import qualified Interpret.Structures.Core as Core
import qualified Interpret.Structures.Numerics as Num
import qualified Interpret.Structures.System as Sys
import qualified Interpret.Structures.Collections as Coll
import qualified Interpret.Structures.Structures as Sct

import Data (Normal, Normal'(NormSct), EvalM)
import qualified Data.Map as Map

coreStructure    = Core.coreStructure
numStructure     = Num.numStructure
systemStructure  = Sys.systemStructure
collStructure    = Coll.collStructure

defaultStructure :: EvalM [(String, Normal)]
defaultStructure = do
  cm <- collStructure
  structs <- Sct.structStructure 
  pure $ insertLeft coreStructure [("num",     NormSct numStructure),
                                   ("sys",     NormSct systemStructure),
                                   ("coll",    NormSct cm),
                                   ("structs", NormSct structs)]
