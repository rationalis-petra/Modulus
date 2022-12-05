{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}
module Parse where

import Control.Monad.Reader (MonadReader)
import Control.Monad.State  (MonadState)
import Control.Monad.Except (MonadError)

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
  
import Data.Text (Text, pack, unpack)
import Data.Void
import qualified Data.Map as Map

import Syntax.Normal
import Interpret.Lib.Data.String (mlsConcat, implShow)

type Parser = Parsec Void Text


-- specials :: Map.Map String (Normal' m)
-- specials = Map.fromList 
--   [ ("→", Special MkProd)
--   , (":", Special Annotate)
--   , (".", Special Access)
--   , ("if", Special If)
--   , ("do", Special Do)
--   , ("quote", Special MkQuote)
--   , ("λ", Special Lambda)
--   , ("let", Special Let)
--   , ("structure", Special MkStructure)
--   , ("signature", Special MkSig)
--   , ("match", Special MkMatch)
--   , ("comatch", Special MkCoMatch)
--   , ("let_open", Special LetOpen)
--   , ("def", Special Def)
--   , ("≜", Special Def)
--   , ("induct", Special Induct)
--   , ("coinduct", Special CoInduct)
--   ]


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
  
pSym :: Parser (Normal m)
pSym = (lexeme $ Symbol <$> pSymStr) <|> (try (between (symbol "(") (symbol ")") pSpecial))
  
pSymStr = (:) <$> (letterChar <|> char '_') <*> many (alphaNumChar <|> char '_' <|> char '-')


pSpecial :: Parser (Normal m)
pSpecial = (lexeme $ Symbol <$> pSpecialStr)
  <|> (try (between (symbol "⧼") (symbol "⧽") pSym)) 

pSpecialStr :: Parser String
pSpecialStr = ((:) <$> specialChar <*> (many $ specialChar))
  where 
    specialChar = (lookAhead $ satisfy (\x -> x /= '\n')) >>
      choice [symbolChar, controlChar, oneOf "!<>:*-+/.,"]
    oneOf :: [Char] -> Parser Char
    oneOf x = choice (map char x)
  
pTightSym :: Parser (Normal m)
pTightSym = lexeme $ Symbol . unpack
  <$> (try (choice [symbol "."]))

pRightSym :: Parser (Normal m)
pRightSym = lexeme $ Symbol . unpack <$> (try (choice [symbol "→", symbol ":"]))


pLiteral :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Parser (AST m)
pLiteral = choice[(Atom <$> (PrimVal <$> choice [pUnit, pBool, pFloat, pInteger])),
                  pString,
                  (Atom <$> pSym)]
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


-- Strings can be template strings, i.e. allow arbitrary code-execution!  
pString :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Parser (AST m)
pString = toStringTemplate <$> lexeme (between (char '"') (char '"') (many (pSubStr <|> pStrVal)))
  where
    toStringTemplate :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => [Either (AST m) String] -> (AST m)
    toStringTemplate = joinall . map toAST
    
    toAST (Left ast)  = Cons [Atom implShow, ast]
    toAST (Right str) = (Atom . PrimVal . String . pack $ str)

    joinall [] = (Atom . PrimVal . String . pack $ "")
    joinall [x] = x
    joinall (x:xs) = Cons [Atom mlsConcat, x, joinall xs]

    pStrVal = Left <$> between (string "${") (string "}") pNormal
    pSubStr :: Parser (Either (AST m) String)
    pSubStr = do
      notFollowedBy (string "\"" <|> string "${")
      Right <$> many (notFollowedBy (string "${") >> satisfy (/= '"'))
    -- (notFollowedBy "${" *> satisfy (\x -> x /= '"'))
  

parens   = between (symbol "(") (symbol ")")
squarens = between (symbol "[") (symbol "]")
larens   = between (symbol "⟨") (symbol "⟩")
curens   = between (symbol "{") (symbol "}")
dcurens  = between (symbol "⦃") (symbol "⦄")
torens   = between (symbol "⦗") (symbol "⦘")

toSeq :: [AST m] -> AST m
--toSeq (Atom val) = Cons [(Atom . Symbol $ "cons"), Atom val, Atom . Symbol $ "nil"]
toSeq [] = Atom . Symbol $ "nil"
toSeq (x:xs) = Cons [(Atom . Symbol $ "cons"), x, toSeq xs]
  

pTerm :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Parser (AST m) 
pTerm = choice [pLiteral,
                (parens pNormal),
                (toSeq <$> torens (many pNormalNoFun)),
                ((\x -> Cons [(Atom $ Keyword "implicit"), x]) <$> curens pNormal),
                ((\x -> Cons [(Atom $ Keyword "instance"), x]) <$> dcurens pNormal),
                squarens (mkCall <$> pNormalNoFun <*> (many pNormalNoFun))]
  where mkCall op args =
          Cons (op : args)


mkOp :: Text -> Parser (AST m -> AST m -> AST m)
mkOp str = (\str x y -> Cons ((Atom . Symbol . unpack) str : [x, y])) <$> symbol str
mkOpP :: Parser (Normal m) -> Parser (AST m -> AST m -> AST m)
mkOpP = (<$>) (\sym x y -> Cons (Atom sym : [x, y]))



pNormalNoFun :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Parser (AST m) 
pNormalNoFun =
  let mkBin :: Parser (AST m) -> Parser (AST m) -> Parser (AST m -> AST m -> AST m) -> Parser (AST m)
      mkBin l r op = (l >>= go) where
        go acc = choice [(((\f x -> f acc x) <$> op <*> r) >>= go), pure acc]

      -- TODO: mkBinTight ++ mkRBin
      sml    = mkBin pTerm  pTerm (mkOpP pTightSym)
      expr   = mkBin sml    sml   (mkOpP pSpecial)
    in expr


pMaybeFunc :: Parser (AST m) -> Parser (AST m)
pMaybeFunc p = maybeFun <$> p  <*> many p
  where maybeFun p [] = p
        maybeFun p xs = Cons (p : xs)


pFunc :: AST m -> Parser (AST m) -> Parser (AST m)  
pFunc v p = mkFun <$> p <*> many p
  where mkFun p [] = p
        mkFun p xs = Cons (v : p : xs)


pNormal :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Parser (AST m)
pNormal = 
  let mkBin l r op = l >>= go where
        go acc = choice [ (((\f x -> f acc x) <$> op <*> pMaybeFunc r) >>= go)
                         , ((mkCall acc
                             <$> r
                             <*> many r) >>= go)
                         , return acc]
      mkBinTight :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => 
                    Parser (AST m) -> Parser (AST m) -> Parser (AST m -> AST m -> AST m) -> Parser (AST m)
      mkBinTight l r op = l >>= go where
        go acc = choice [(((\f x -> f acc x) <$> op <*> r) >>= go), return acc]
  
      mkRBin l r op = l >>= go where
        go acc = choice [ ((\f x -> f acc x) <$> op <*> mkRBin l r op)
                        , ((mkCall acc
                             <$> r
                             <*> many r) >>= go)
                        , return acc]

      mkCall op arg args = Cons (op : (arg : args))

      sml    = mkBinTight  pTerm  pTerm (mkOp ".")
      ty     = mkRBin      sml    sml   (mkOpP pRightSym)
      expr   = mkBin       ty     ty    (mkOpP pSpecial)
    in expr


pHeader = do
  pHeaderDecl  
  imports <- try (parens pImports) <|> pure []
  foreignLibs <- try (parens pForeign) <|> pure []
  exports <- try (parens pExports) <|> pure []
  pure (imports, foreignLibs, exports, [])
  where
    pHeaderDecl = do 
      symbol "module"
      pSymStr
      pure ()

    pImports = do
      symbol "import"
      many pSymStr

    pForeign = do
      symbol "foreign"
      many pForeignTerm
        where
          pForeignTerm = parens ((,) <$> lexeme pSymStr <*> pString)

    pExports = do
      symbol "export"
      many pSymStr

    pString :: Parser String
    pString = lexeme $ between (char '"') (char '"') (many $ satisfy (/= '"'))

    pSymStr =
      lexeme $ (:) <$> (letterChar <|> char '_') <*> many (alphaNumChar <|> char '_' <|> char '-')
 

pTop :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Parser [AST m]
pTop = sc *> try (many (parens pNormal)) <* sc


data ReplMessage
  = Quit
  | ToggleType
  | Continue
  | LoadForeign String
  
  
pPreRepl :: Parser ReplMessage 
pPreRepl = choice
  [ ((string ":q") >> pure Quit)
  , ((string ":t") >> pure ToggleType)
  , (LoadForeign <$> (symbol ":foreign" >> pLibStr))
  , (many (satisfy (const True)) >> pure Continue)
  ]
  where 
    pLibStr = (:) <$> (letterChar <|> char '_') <*> many (alphaNumChar <|> oneOf "_-.")

    oneOf :: [Char] -> Parser Char
    oneOf x = choice (map char x)


pRepl :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Parser (AST m)
pRepl = sc *> pNormal

pMod :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Parser (([String], [(String, String)], [String], [a]), [AST m])
pMod = do
  sc
  header <- parens pHeader
  defs <- pTop
  eof
  pure (header, defs)

  
parsePreRepl = runParser (pPreRepl <* eof)


parseScript :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => String -> Text -> Either (ParseErrorBundle Text Void) [AST m]
parseScript = runParser (pTop <* eof)


parseRepl :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => String -> Text -> Either (ParseErrorBundle Text Void) (AST m)
parseRepl = runParser (pRepl <* eof)

-- parseModule :: String -> Text -> Either (String AST
parseModule :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => String -> Text -> Either (ParseErrorBundle Text Void) (([String], [(String, String)], [String], [a]), [AST m])
parseModule = runParser (pMod <* eof) 

