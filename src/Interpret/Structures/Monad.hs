module Interpret.Structures.Monad (monadStructure, monadSignature) where 

import Data
import Interpret.Structures.Monad.IO

  
monadSignature :: Normal
monadSignature = NormSig [("io", ioMonadSignature)]

monadStructure :: Normal
monadStructure = NormSct [("io", ioMonadStructure)] monadSignature
 

