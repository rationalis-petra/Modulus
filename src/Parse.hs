{-# LANGUAGE OverloadedStrings #-}
module Parse where

import Data
import Interpret.Eval (Expr)
  
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
  
import Data.Text (Text, pack, unpack)
import Data.Void

type Parser = Parsec Void Text



sc :: Parser ()  
sc = L.space
  space1
  (L.skipLineComment "#")
  (L.skipBlockComment "#(" ")#")
  
lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text  
symbol = L.symbol sc

many1 :: Parser a -> Parser [a]
many1 p = (:) <$> p <*> (many p)
  
pSym :: Parser Expr
pSym = (lexeme $ Symbol <$> pSymStr) <|> (try (between (symbol "`") (symbol "`") pSpecial))
  where
    pSymStr = (:) <$> (letterChar <|> char '_') <*> many (alphaNumChar <|> char '-' <|> char '_')

pSpecial :: Parser Expr
pSpecial = (lexeme $ Symbol <$> pSpecialStr)
  <|> (try (between (symbol "`") (symbol "`") pSym)) 

pSpecialStr :: Parser String
pSpecialStr = ((:) <$> specialChar <*> (many $ specialChar))
  where 
    specialChar = (lookAhead $ satisfy (\x -> x /= '`' && x /= '\n')) >>
      choice [symbolChar, controlChar, oneOf "!<>:*-+/.,"]
    oneOf :: [Char] -> Parser Char
    oneOf x = choice (map char x)
  
pTightSym :: Parser Expr
pTightSym = lexeme $ Symbol . unpack
  <$> (try (choice [symbol ".", symbol "<:"]))

pRightSym :: Parser Expr
pRightSym = lexeme $ Symbol . unpack <$> (try (choice [symbol "→", symbol ":"]))


pLiteral :: Parser Expr
pLiteral = (PrimVal <$> choice [pUnit, pBool, pFloat, pInteger, pString])
           <|> pSym
  where
    pBool = Bool <$> (pTrue <|> pFalse) 
      where
        pTrue = symbol "True" *> return True
        pFalse = symbol "False" *> return False
  
    sign :: Num a => Parser a -> Parser a 
    sign p = (try (char '-') >> ((\x -> -x) <$> p)) <|> p
    pInteger = Int <$> (try $ lexeme $ sign L.decimal)
    pFloat = Float <$> (try $ lexeme $ sign L.float)
    pUnit = try (symbol "()") *> return Unit

    pString = (String . pack)
      <$> (lexeme (between (char '"') (char '"') (many $ satisfy (\x -> x /= '"'))))

  

parens   = between (symbol "(") (symbol ")")
squarens = between (symbol "[") (symbol "]")
curens   = between (symbol "{") (symbol "}")


pTerm :: Parser AST 
pTerm = choice [Atom <$> pLiteral,
                (parens pExpr),
                -- (curens pExpr),
                ((\x -> Cons [(Atom $ Keyword "implicit"), x]) <$> curens pExpr),
                squarens (mkCall <$> pExprNoFun <*> (many pExprNoFun))]
  where mkCall op args =
          Cons (op : args)


mkOp str = (\str x y ->
              Cons [(Atom $ Symbol (unpack str)), x, y]) <$>
           symbol str
mkOpP :: Parser Expr -> Parser (AST -> AST -> AST)
mkOpP = (<$>) (\sym x y -> Cons [(Atom sym), x, y])



pExprNoFun :: Parser AST 
pExprNoFun =
  let mkBin :: Parser AST -> Parser (AST -> AST -> AST) -> Parser AST
      mkBin e op = e >>= go where
        go :: AST -> Parser AST
        go acc = choice [(((\f x -> f acc x) <$> op <*> e) >>= go),
                         return acc]
  -- TODO: mkBinTight ++ mkRBin

      sml = mkBin pTerm (mkOpP pTightSym) -- (symbol "::" >> pure Annotation)
      factor = mkBin sml (mkOp "*" <|> mkOp "/")
      arith = mkBin factor (mkOp "+" <|> mkOp "-")
      expr = mkBin arith (mkOpP pSpecial)
    in expr

pExpr :: Parser AST 
pExpr = 
  let mkBin e op = e >>= go where
        go :: AST -> Parser AST
        go acc = choice [(((\f x -> f acc x) <$> op <*> e) >>= go),
                         ((mkCall acc
                           <$> e
                           <*> many e) >>= go),
                         return acc]
      mkBinTight e op = e >>= go where
        go :: AST -> Parser AST
        go acc = choice [(((\f x -> f acc x) <$> op <*> e) >>= go), return acc]

      mkRBin :: Parser AST -> Parser (AST -> AST -> AST) -> Parser AST
      mkRBin e op = e >>= go where
        go :: AST -> Parser AST
        go acc = choice [((\f x -> f acc x) <$> op <*> mkRBin e op),
                         return acc]
  

      mkCall op arg args =
          Cons (op : (arg :args))


  in
    let sml = mkBinTight pTerm (mkOpP pTightSym)
        factor = mkBin sml (mkOp "∙" <|> mkOp "/")
        arith = mkBin factor (mkOp "+" <|> mkOp "-")
        ty = mkRBin factor (mkOp "→")
        expr = mkBin ty (mkOpP pSpecial)
    in expr

 
-- pExpr :: Parser AST
-- pExpr = makeExprParser pTerm operatorTable

pTop :: Parser [AST]
pTop = sc *> try (many (parens pExpr)) <* sc

pRepl :: Parser AST
pRepl = sc *> pExpr

pMod :: Parser AST
pMod = sc *> parens pExpr <* sc

parseFile = runParser (pTop <* eof)
parseRepl = runParser (pRepl <* eof)
parseModule = runParser (pMod <* eof)
