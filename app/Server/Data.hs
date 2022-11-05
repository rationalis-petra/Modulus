{-# LANGUAGE TemplateHaskell #-}
module Server.Data where 

import Control.Lens (makeLenses)

import Data (Normal, Definition, Environment, ProgState) 
import Data.Text (Text)
import qualified Data.Map as Map

data ModuleHeader = ModuleHeader { _imports :: [String],
                                   _args    :: [String],
                                   _exports :: [String] }

data Module = Module { _vals :: [(String, Normal)],
                       _types :: [(String, Normal)],
                       _header :: ModuleHeader,
                       _sourceCore :: [Definition],
                       _sourceString :: Text  }

instance Show Module where    
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
type ModuleTree = DTree String Module




data IState = IState { _progState   :: ProgState,
                       _environment :: Environment,
                       _modules     :: Either RawTree ModuleTree }

$(makeLenses ''IState)
$(makeLenses ''Module)
$(makeLenses ''ModuleHeader)



  
