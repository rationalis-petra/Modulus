{-# LANGUAGE FlexibleContexts #-}
module Interpret.Lib.System (systemStructure, systemSignature) where

import Control.Monad.State (MonadState)
import Control.Monad.Except (MonadError)
import Control.Monad.Reader (MonadReader)
import Syntax.Normal

import Interpret.Lib.System.Console

  
systemSignature :: Normal m
systemSignature = NormSig $ [("console", consoleSignature)]

systemStructure :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
systemStructure = NormSct (toEmpty
                  [ ("console", consoleStructure) 
                  ]) systemSignature
