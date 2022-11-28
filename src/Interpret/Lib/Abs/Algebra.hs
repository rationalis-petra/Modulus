module Interpret.Lib.Abs.Algebra where

import Syntax.Normal  

import Interpret.Lib.Abs.Algebra.Semigroup
import Interpret.Lib.Abs.Algebra.Ring
import Interpret.Lib.Abs.Algebra.Field


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
