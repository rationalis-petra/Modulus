module Interpret.Lib.LibUtils where

import Syntax.Normal

tyTail :: (Normal m) -> (Normal m)
tyTail (NormArr l r) = r
tyTail (NormProd sym a b) = b
tyTail (NormImplProd sym a b) = b
