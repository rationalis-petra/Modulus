{-# LANGUAGE FlexibleContexts #-}
module Interpret.Lib.Abs where

import Interpret.Lib.Abs.Algebra
import Syntax.Normal

  


absSignature :: Normal m
absSignature = NormSig
  [ ("algebra", algebraSignature)
  ]

  
absStructure :: Normal m
absStructure = NormSct (toEmpty
  [ ("algebra", algebraStructure)
  ]) absSignature
