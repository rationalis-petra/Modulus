module Interpret.Lib.Algebra where

import Data  

import Interpret.Lib.Algebra.Semigroup
import Interpret.Lib.Algebra.Ring


algebraSignature :: Normal
algebraSignature = NormSig
  [ ("semigroup", semigroupSignature)
  , ("ring", ringSignature)
  ]

  
algebraStructure :: Normal
algebraStructure = NormSct (toEmpty
  [ ("semigroup", semigroupStructure)
  , ("ring", ringStructure)
  ]) algebraSignature
