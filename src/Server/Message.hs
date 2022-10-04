module Server.Message where

import Data.Text (Text, pack)
import Data.Void
import Text.Megaparsec  
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

data Message
  = UpdateModule [String] Text
  | Compile
  | RunMain
  | Kill

type Parser = Parsec Void String

symbol = L.symbol (pure ())  

parse :: String -> Maybe Message
parse str = case runParser pMessage "message" str of 
  Right val -> Just val
  Left _ -> Nothing


pMessage :: Parser Message  
pMessage = choice [pKill, pRunMain, pUpdateModule]
    
pKill :: Parser Message
pKill = do
  symbol "Kill"
  pure Kill

pRunMain :: Parser Message
pRunMain = do
  symbol "RunMain"
  pure RunMain
  
pUpdateModule :: Parser Message
pUpdateModule = do
  symbol "UpdateModule"
  path <- between (symbol "[") (symbol "]")
            ((:) <$> pSymbol <*> many (symbol "," *> pSymbol))
  body <- pack <$> (many (satisfy (\_ -> True)) <* eof)
  pure $ UpdateModule path body


pSymbol :: Parser String  
pSymbol = many alphaNumChar
