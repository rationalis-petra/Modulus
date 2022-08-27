module Interpret.Modules.Collections (collModule) where

import Control.Monad.Except (throwError, catchError)

import Interpret.Modules.Collections.String (stringModule) 
import Interpret.Modules.Collections.List   (listModule) 
import Interpret.Modules.Collections.Vector (vectorModule) 

import qualified Data.Map as Map
import Data


  
collModule :: EvalM [(String, Normal)]
collModule = do
  lm <- listModule
  pure $  [("String",  stringModule),
           ("List",    lm),
           ("Vector",  vectorModule)]
