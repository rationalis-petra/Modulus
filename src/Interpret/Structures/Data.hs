module Interpret.Structures.Data (dataStructure, dataSignature) where

import Control.Monad.Except (throwError, catchError)

import Interpret.Structures.Data.String
import Interpret.Structures.Data.List
import Interpret.Structures.Data.Maybe
import Interpret.Structures.Data.Array

import qualified Data.Map as Map
import Data

dataSignature :: Normal
dataSignature = NormSig
                [ ("string", stringSignature)
                , ("list",   listSignature)
                , ("array",  arraySignature)
                , ("maybe",  maybeSignature)
                ]
                
  
dataStructure :: Normal
dataStructure = NormSct (toEmpty
                [ ("string", stringStructure)
                , ("list",   listStructure)
                , ("array",  arrayStructure)
                , ("maybe",  maybeStructure)
                ]) dataSignature
