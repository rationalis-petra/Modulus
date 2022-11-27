module Interpret.Lib.Algebra where

import Data  

import Interpret.Lib.Algebra.Semigroup
import Interpret.Lib.Algebra.Ring
import Interpret.Lib.Algebra.Field


algebraSignature :: Normal m
algebraSignature = NormSig
  [ ("semigroup", semigroupSignature)
  , ("ring", ringSignature)
  , ("field", fieldSignature)
  ]

  
algebraStructure :: Normal m
algebraStructure = NormSct (toEmpty
  [ ("semigroup", semigroupStructure)
  , ("ring", ringStructure)
  , ("field", ringStructure)
  ]) algebraSignature
