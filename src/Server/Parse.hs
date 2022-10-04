{-# LANGUAGE OverloadedStrings #-}
module Server.Parse where

import Data
-- import Interpret.Eval (Normal'(..), Normal)
  
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
  
import Data.Text (Text, pack, unpack)
import Data.Void

type Parser = Parsec Void Text


-- parse server network packets  
