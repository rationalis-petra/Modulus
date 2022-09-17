module Interpret.Structures where


import Control.Monad.State (State)

import Syntax.Utils  

import qualified Interpret.Structures.Core as Core
import qualified Interpret.Structures.Numerics as Num
import qualified Interpret.Structures.System as Sys
import qualified Interpret.Structures.Collections as Coll
import qualified Interpret.Structures.Structures as Sct

import Data (Normal, Normal'(NormSct, NormSig), EvalM)
import qualified Data.Map as Map

coreStructure    = Core.coreStructure
numStructure     = Num.numStructure
numSignature     = Num.numSignature
systemStructure  = Sys.systemStructure
systemSignature  = Sys.systemSignature
collStructure    = Coll.collStructure
collSignature    = Coll.collSignature

defaultStructure :: EvalM [(String, Normal)]
defaultStructure = do
  cm <- collStructure
  structs <- Sct.structStructure 
  pure $ insertLeft coreStructure [("num",     NormSct numStructure numSignature),
                                   ("sys",     NormSct systemStructure systemSignature),
                                   ("coll",    NormSct cm collSignature),
                                   ("structs", NormSct structs (NormSig []))]
