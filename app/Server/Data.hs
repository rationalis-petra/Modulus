{-# LANGUAGE TemplateHaskell #-}
module Server.Data where 

import Control.Lens (makeLenses)

import Data (Normal, Environment, ProgState)
import Syntax.Core(Core(..), Definition)
import Data.Text (Text)
import qualified Data.Map as Map

data ModuleHeader = ModuleHeader { _imports :: [String],
                                   _args    :: [String],
                                   _exports :: [String] }

data Module m = Module { _vals :: [(String, Normal m)],
                       _types :: [(String, Normal m)],
                       _header :: ModuleHeader,
                       _sourceCore :: [Definition m],
                       _sourceString :: Text  }

instance Show (Module m) where    
  show Module { _vals=vals } = showVals vals
    where
      showVals [] = ""
      showVals [(string, normal)] = "(def " <> show string <> "\n" <> show normal <> ")"
      showVals ((string, normal) : defs) = 
        "(def " <> show string <> "\n" <> show normal <> ")" <> "\n\n" <> showVals defs

data DTree a b = Node (Map.Map a (DTree a b)) (Maybe b)
  deriving Show
emptyTree :: DTree a b
emptyTree = Node Map.empty Nothing

type RawTree = DTree String Text
type ModuleTree m = DTree String (Module m)




data IState m = IState { _progState   :: ProgState m,
                         _environment :: Environment m,
                         _modules     :: Either RawTree (ModuleTree m) }

$(makeLenses ''IState)
$(makeLenses ''Module)
$(makeLenses ''ModuleHeader)



  
