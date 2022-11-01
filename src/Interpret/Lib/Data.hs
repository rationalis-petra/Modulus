module Interpret.Lib.Data (dataStructure, dataSignature) where

import Control.Monad.Except (throwError, catchError)

import Interpret.Lib.Data.String
import Interpret.Lib.Data.List
import Interpret.Lib.Data.Maybe
import Interpret.Lib.Data.Array

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
