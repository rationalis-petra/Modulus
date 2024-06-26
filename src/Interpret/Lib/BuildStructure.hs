{-# LANGUAGE FlexibleContexts #-}
module Interpret.Lib.BuildStructure where

import qualified Data.Map as Map
import Control.Monad.State (MonadState)
import Control.Monad.Except (MonadError)
import Control.Monad.Reader (MonadReader)

import Syntax.Normal(ProgState,
                     Normal(NormSct, NormSig),
                     toEmpty)
import Interpret.Environment (Environment(..)) 
import Interpret.Lib.Core (coreTerms) 


moduleContext :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Environment m
moduleContext = Environment
  { localInstances = []
  , localCtx = Map.empty
  , currentModule = NormSct (toEmpty coreTerms) (NormSig [])
  , globalModule = NormSct [] (NormSig [])
  }
