module Interpret.Lib.Monad (monadStructure, monadSignature) where 

import Data
import Interpret.Lib.Monad.IO

  
monadSignature :: Normal
monadSignature = NormSig
                 [ ("io", ioMonadSignature)
                 ]

monadStructure :: Normal
monadStructure = NormSct (toEmpty
                 [ ("io", ioMonadStructure)
                 ]) monadSignature
 

