{-# LANGUAGE FlexibleContexts #-}
module Interpret.Lib.Foreign where

import Control.Monad.Reader (MonadReader)
import Control.Monad.State  (MonadState)
import Control.Monad.Except (MonadError)

import Data
import Interpret.Lib.Foreign.C


foreignSignature :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
foreignSignature = NormSig
  [ ("c", csignature)
  ]

foreignStructure :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m  
foreignStructure = NormSct (toEmpty
  [ ("c", cstructure)
  ]) foreignSignature
