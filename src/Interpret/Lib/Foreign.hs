module Interpret.Lib.Foreign where

import Data
import Interpret.Lib.Foreign.C


foreignSignature :: Normal  
foreignSignature = NormSig
  [ ("c", csignature)
  ]

foreignStructure :: Normal  
foreignStructure = NormSct (toEmpty
  [ ("c", cstructure)
  ]) foreignSignature
