module Interpret.Lib.LibUtils where

import Syntax.Normal

tyTail :: (Normal m) -> (Normal m)
tyTail (NormArr _ r) = r
tyTail (NormProd _ _ _ b) = b
