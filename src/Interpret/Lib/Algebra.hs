module Interpret.Lib.Algebra where

import Data  

import Interpret.Lib.Algebra.Semigroup


algebraSignature :: Normal
algebraSignature = NormSig
  [ ("semigroup", semiGroupSignature)
  ]

  
algebraStructure :: Normal
algebraStructure = NormSct (toEmpty
  [ ("semigroup", semiGroupStructure)
  ]) algebraSignature
