module Interpret.Structures.Monad.IO (ioMonadStructure, ioMonadSignature) where

import Data

ioMonadSignature :: Normal
ioMonadSignature = NormSig []

ioMonadStructure :: Normal
ioMonadStructure = NormSct [] ioMonadSignature
