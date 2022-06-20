module Interpret.Modules.Collections (collModule) where

import Control.Monad.Except (throwError, catchError)

import Interpret.Modules.Collections.String (stringModule) 
import Interpret.Modules.Collections.List   (listModule) 
import Interpret.Modules.Collections.Vector (vectorModule) 

import qualified Data.Map as Map
import Data


  
collModule :: EvalM (Map.Map String Expr)
collModule = do
  lm <- listModule
  pure $ Map.fromList [("String",   stringModule),
                       ("List",    lm),
                       ("Vector",  vectorModule)]
