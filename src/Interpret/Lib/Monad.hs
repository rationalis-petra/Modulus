{-# LANGUAGE FlexibleContexts #-}
module Interpret.Lib.Monad (monadStructure, monadSignature) where 

import Control.Monad.Reader (MonadReader)
import Control.Monad.State  (MonadState)
import Control.Monad.Except (MonadError)

import Data
import Interpret.Lib.Monad.IO

   
monadSignature :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
monadSignature = NormSig
                 [ ("io", ioMonadSignature)
                 ]

monadStructure :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
monadStructure = NormSct (toEmpty
                 [ ("io", ioMonadStructure)
                 ]) monadSignature
 

