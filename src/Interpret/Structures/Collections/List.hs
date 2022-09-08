module Interpret.Structures.Collections.List (listStructure) where

import Control.Monad.Except (throwError, catchError)

import qualified Data.Map as Map

import qualified Data.Map as Map
import Data
import Interpret.Transform
import Interpret.Structures.BuildStructure

listStructureSource = "\
\ (structure \
\  (induct (List [A : 𝒰] : 𝒰) \
\    (cons : A  → List A) \
\    (nil : List A)))"


listStructure :: EvalM Normal
listStructure = 
  buildModule Map.empty listStructureSource
