{-# LANGUAGE OverloadedStrings #-}
module Server.Message where

import Data.Text (Text, pack)
import Data.Void
import Text.Megaparsec  
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

data Message
  -- updates
  = UpdateModule [String] Text

  -- queries
  | Describe [String]

  -- commands
  | Compile
  | RunMain
  | Kill
  deriving Show

type Parser = Parsec Void Text

symbol = L.symbol (pure ())  

parse :: Text -> Maybe Message
parse str = case runParser pMessage "message" str of 
  Right val -> Just val
  Left _ -> Nothing


pMessage :: Parser Message  
pMessage = choice [pKill, pRunMain, pCompile, pUpdateModule]
    
pKill :: Parser Message
pKill = do
  symbol "Kill"
  pure Kill

pRunMain :: Parser Message
pRunMain = do
  symbol "RunMain"
  pure RunMain

pCompile :: Parser Message
pCompile = do
  symbol "Compile"
  pure Compile

pDescribe :: Parser Message  
pDescribe = do
  symbol "Describe"
  symbol " "
  path <- between (symbol "[") (symbol "]") (pure [])
  pure $ Describe path
  
pUpdateModule :: Parser Message
pUpdateModule = do
  symbol "UpdateModule"
  symbol " "
  path <- between (symbol "[") (symbol "]") (pure [])
            -- (try ((:) <$> pSymbol <*> many (symbol "," *> pSymbol)) <|> pure [])
  symbol " "
  body <- pack <$> (many (satisfy (\_ -> True)) <* eof)
  pure $ UpdateModule path body


pSymbol :: Parser String  
pSymbol = (try ((:) <$> alphaNumChar <*> many alphaNumChar) <|> pure [])
