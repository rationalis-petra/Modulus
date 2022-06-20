module Interpret.Modules where


import Control.Monad.State (State)

import qualified Interpret.Modules.Core as Core
import qualified Interpret.Modules.Numerics as Num
import qualified Interpret.Modules.System as Sys
import qualified Interpret.Modules.Collections as Coll
import qualified Interpret.Modules.Structures as Sct

import Data (Expr, ModulusType, EvalM)
import qualified Data.Map as Map

coreModule = Core.coreModule
numModule  = Num.numModule
systemModule  = Sys.systemModule
collModule  = Coll.collModule

defaultModule :: EvalM (Map.Map String Expr)
defaultModule = do
  cm <- collModule
  structs <- Sct.structModule 
  pure $ foldr Map.union coreModule [numModule, systemModule, cm, structs]
