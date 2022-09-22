{-# LANGUAGE OverloadedStrings #-}
module Parse where

import Data
-- import Interpret.Eval (Normal'(..), Normal)
  
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
  
import Data.Text (Text, pack, unpack)
import Data.Void

type Parser = Parsec Void Text



sc :: Parser ()  
sc = L.space
  space1
  (L.skipLineComment ";;")
  (L.skipBlockComment ";;(" ");;")
  
lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text  
symbol = L.symbol sc

many1 :: Parser a -> Parser [a]
many1 p = (:) <$> p <*> (many p)
  
pSym :: Parser Normal
pSym = (lexeme $ Symbol <$> pSymStr) <|> (try (between (symbol "(") (symbol ")") pSpecial))
  where
    pSymStr = (:) <$> (letterChar <|> char '_') <*> many (alphaNumChar <|> char '_')


pSpecial :: Parser Normal
pSpecial = (lexeme $ Symbol <$> pSpecialStr)
  <|> (try (between (symbol "`") (symbol "`") pSym)) 

pSpecialStr :: Parser String
pSpecialStr = ((:) <$> specialChar <*> (many $ specialChar))
  where 
    specialChar = (lookAhead $ satisfy (\x -> x /= '`' && x /= '\n')) >>
      choice [symbolChar, controlChar, oneOf "!<>:*-+/.,"]
    oneOf :: [Char] -> Parser Char
    oneOf x = choice (map char x)
  
pTightSym :: Parser Normal
pTightSym = lexeme $ Symbol . unpack
  <$> (try (choice [symbol ".", symbol "<:"]))

pRightSym :: Parser Normal
pRightSym = lexeme $ Symbol . unpack <$> (try (choice [symbol "→", symbol ":"]))


pLiteral :: Parser Normal
pLiteral = (PrimVal <$> choice [pUnit, pBool, pFloat, pInteger, pString])
           <|> pSym
  where
    pBool = Bool <$> (pTrue <|> pFalse) 
      where
        pTrue = symbol "true" *> return True
        pFalse = symbol "false" *> return False
  
    sign :: Num a => Parser a -> Parser a 
    sign p = (try (char '-') >> ((\x -> -x) <$> p)) <|> p
    pInteger = Int <$> (try $ lexeme $ sign L.decimal)
    pFloat = Float <$> (try $ lexeme $ sign L.float)
    pUnit = try (symbol "()") *> return Unit

    pString = (String . pack)
      <$> (lexeme (between (char '"') (char '"') (many $ satisfy (\x -> x /= '"'))))

  

parens   = between (symbol "(") (symbol ")")
squarens = between (symbol "[") (symbol "]")
larens   = between (symbol "⟨") (symbol "⟩")
curens   = between (symbol "{") (symbol "}")


pTerm :: Parser AST 
pTerm = choice [Atom <$> pLiteral,
                (parens pNormal),
                ((\x -> Cons [(Atom $ Keyword "implicit"), x]) <$> curens pNormal),
                squarens (mkCall <$> pNormalNoFun <*> (many pNormalNoFun))]
  where mkCall op args =
          Cons (op : args)


mkOp :: Text -> Parser ([AST] -> AST -> AST)
mkOp str = (\str x y ->
              Cons ([(Atom . Symbol . unpack) str] <> x <> [y])) <$> symbol str
mkOpP :: Parser Normal -> Parser ([AST] -> AST -> AST)
mkOpP = (<$>) (\sym x y -> Cons ([Atom sym] <> x <> [y]))



pNormalNoFun :: Parser AST 
pNormalNoFun =
  let mkBin :: Parser (Either AST [AST]) -> Parser AST -> Parser ([AST] -> AST -> AST) -> Parser AST
      mkBin l r op = (l >>= go0) where
        go0 :: Either AST [AST] -> Parser AST
        go0 acc = choice [(((\f x -> f (case acc of Left ast -> [ast]; Right lst -> lst) x)
                              <$> op <*> r) >>= go1),
                          pure (case acc of Left ast -> ast; Right lst -> Cons lst)]

        go1 :: AST -> Parser AST
        go1 acc = choice [(((\f x -> f [acc] x) <$> op <*> r) >>= go1), pure acc]
      mkBin' :: Parser AST -> Parser ([AST] -> AST -> AST) -> Parser AST
      mkBin' = mkBin (((\v -> case v of Cons l -> Right l; x -> Right [x]) <$> larens pNormal)
                      <|> (\x -> Left x) <$> pTerm)

      -- TODO: mkBinTight ++ mkRBin
      sml    = mkBin' pTerm  (mkOpP pTightSym)
      expr   = mkBin' sml    (mkOpP pSpecial)
    in expr

pNormal :: Parser AST 
pNormal = 
  let mkBin' l r op = l >>= go0 where
        go0 :: Either AST [AST] -> Parser AST
        go0 acc = choice [(((\f x -> f (toLst acc) x) <$> op <*> r) >>= go1),
                         ((mkCall [(toVal acc)]
                           <$> r
                           <*> many r) >>= go1),
                         return (toVal acc)]
        go1 :: AST -> Parser AST
        go1 acc = choice [(((\f x -> f [acc] x) <$> op <*> r) >>= go1),
                         ((mkCall [acc]
                           <$> r
                           <*> many r) >>= go1),
                         return acc]
      mkBin = mkBin' pLeft
      pLeft = (((\v -> case v of Cons l -> Right l; x -> Right [x]) <$> larens pNormal)
                 <|> (\x -> Left x) <$> pTerm)

      mkBinTight' l r op = l >>= go0 where
        go0 :: Either AST [AST] -> Parser AST
        go0 acc = choice [(((\f x -> f (toLst acc) x) <$> op <*> r) >>= go1), return (toVal acc)]

        go1 :: AST -> Parser AST
        go1 acc = choice [(((\f x -> f [acc] x) <$> op <*> r) >>= go1), return acc]
      mkBinTight = mkBinTight' pLeft
      pRLeft = (((\v -> case v of Cons l -> Right l; x -> Right [x]) <$> larens pNormal)
                 <|> (\x -> Left x) <$> sml)

      mkRBin' :: Parser (Either AST [AST]) -> Parser AST -> Parser ([AST] -> AST -> AST) -> Parser AST
      mkRBin' l r op = l >>= go where
        go :: Either AST [AST] -> Parser AST
        go acc = choice [((\f x -> f (toLst acc) x) <$> op <*> mkRBin' l r op),
                         return (toVal acc)]
      mkRBin = mkRBin' pRLeft

      toLst v = case v of Left x -> [x]; Right lst -> lst
      toVal v = case v of Left x -> x;   Right lst -> Cons lst

      mkCall op arg args =
          Cons (op <> (arg : args))

  
      sml    = mkBinTight pTerm (mkOp ".")
      ty     = mkRBin sml     (mkOp "→")
      expr   = mkBin  ty    (mkOpP pSpecial)
    in expr

 
-- pNormal :: Parser AST
-- pNormal = makeNormalParser pTerm operatorTable

pTop :: Parser [AST]
pTop = sc *> try (many (parens pNormal)) <* sc

pRepl :: Parser AST
pRepl = sc *> pNormal

pMod :: Parser AST
pMod = sc *> parens pNormal <* sc

parseFile = runParser (pTop <* eof)
parseRepl = runParser (pRepl <* eof)
parseModule = runParser (pMod <* eof)
