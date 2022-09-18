module Interpret.Structures.Collections (collStructure, collSignature) where

import Control.Monad.Except (throwError, catchError)

import Interpret.Structures.Collections.String (stringStructure, stringSignature) 
import Interpret.Structures.Collections.List   (listStructure, listSignature) 
import Interpret.Structures.Collections.Array  (arrayStructure, arraySignature) 

import qualified Data.Map as Map
import Data

collSignature :: Normal
collSignature = NormSig [("string", stringSignature),
                         ("list",   listSignature),
                         ("array",  arraySignature)]
  
collStructure :: Normal
collStructure = NormSct [("string", stringStructure),
                         ("list",   listStructure),
                         ("array",  arrayStructure)] collSignature
