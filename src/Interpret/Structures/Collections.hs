module Interpret.Structures.Collections (collStructure, collSignature) where

import Control.Monad.Except (throwError, catchError)

import Interpret.Structures.Collections.String (stringStructure, stringSignature) 
import Interpret.Structures.Collections.List   (listStructure) 
import Interpret.Structures.Collections.Array  (arrayStructure) 

import qualified Data.Map as Map
import Data

collSignature :: Normal
collSignature = NormSig [("string", stringSignature)]
           -- ("list",    lm),
           -- ("array",  arrayStructure)]
  
collStructure :: EvalM [(String, Normal)]
collStructure = do
  lm <- listStructure
  pure $  [("string",  stringStructure),
           ("list",    lm),
           ("array",  arrayStructure)]
