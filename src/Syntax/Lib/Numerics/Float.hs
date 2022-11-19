module Syntax.Lib.Numerics.Float where

  
data FloatLib 
  = FloatAdd
  | FloatSub
  | FloatMul
  | FloatDiv
  | FloatExp

  | FloatShow

  | FloatEq
  | FloatNeq
  | FloatLess
  | FloatLeq
  | FloatGreater
  | FloatGrEq
  deriving (Show, Eq, Ord)
