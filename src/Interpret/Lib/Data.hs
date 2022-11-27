{-# LANGUAGE FlexibleContexts #-}
module Interpret.Lib.Data (dataStructure, dataSignature) where

import Control.Monad.Reader (MonadReader)
import Control.Monad.State  (MonadState)
import Control.Monad.Except (MonadError)

import Interpret.Lib.Data.String
import Interpret.Lib.Data.List
import Interpret.Lib.Data.Maybe
import Interpret.Lib.Data.Array

import qualified Data.Map as Map
import Data

dataSignature :: Normal m
dataSignature = NormSig
                [ ("string", stringSignature)
                , ("list",   listSignature)
                , ("array",  arraySignature)
                , ("maybe",  maybeSignature)
                ]
                
  
dataStructure :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
dataStructure = NormSct (toEmpty
                [ ("string", stringStructure)
                , ("list",   listStructure)
                , ("array",  arrayStructure)
                , ("maybe",  maybeStructure)
                ]) dataSignature
