module PEGParser where 

import Control.Applicative.Combinators hiding (many, someTill, endBy)
import Control.Monad.Combinators.Expr 
import Control.Monad (void)
import Data.Void 
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import ParserExpression


type Parser = Parsec Void String

-- top level grammar parser 

parser :: String -> Either String Grammar 
parser s = case parse parseGrammar "" s of 
              Left err -> Left $ errorBundlePretty err 
              Right g  -> Right g

parseGrammar :: Parser Grammar 
parseGrammar = Grammar <$> parseRules <*> parseStart 

-- parser for rules 

parseRules :: Parser [(String, Expr)]
parseRules = (f <$> identifier     <*> 
                    reserved "<--" <*> 
                  parseExpr) 
            `endBy` semi 
      where  
        f v _ e = (v,e)

-- parser for the starting expression 

parseStart :: Parser Expr 
parseStart = reserved "@start:" *> parseExpr

-- parsing for symbols 

parseString :: Parser Expr
parseString 
  = f <$> (symbol "\"" *> someTill L.charLiteral (symbol "\""))
    where 
      f = foldr1 (:@:) . map Chr

-- parsing for variables 

parseVar :: Parser Expr 
parseVar = NT <$> identifier 

-- parsing for factors 

parseFactor :: Parser Expr 
parseFactor
  = makeExprParser parseAtom table 

-- parser for non-terminals, terminals and parenthesis

parseAtom :: Parser Expr 
parseAtom = parseVar <|> parseString <|> parens parseExpr  

-- parser for concatenation: spaces is mandatory

parseTerm :: Parser Expr 
parseTerm = chainr1 parseFactor $ do 
                space 
                return (:@:)

-- parser for choice

parseExpr :: Parser Expr 
parseExpr = chainr1 parseTerm $ do 
               reserved "/"
               return (:/:)

-- precedence table for star / negation

table :: [[Operator Parser Expr]]
table = [
           [
              postfix "*" Star
           ]
        , 
           [
              prefix "!" Not 
           ]
        ]

prefix, postfix :: String -> (Expr -> Expr) -> Operator Parser Expr
prefix  name f = Prefix  (f <$ symbol name)
postfix name f = Postfix (f <$ symbol name)

-- definition of the lexer 

sc :: Parser ()
sc = L.space (void spaceChar) lineCmnt blockCmnt
  where lineCmnt  = L.skipLineComment "--"
        blockCmnt = L.skipBlockComment "/-" "-/"

-- function for creating lexemes

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

-- 'parens' parses something between parenthesis.

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- 'semi' parses a semicolon.

semi :: Parser String
semi = symbol ";"

-- parsing reserved words 

reserved :: String -> Parser ()
reserved w = lexeme (string w *> notFollowedBy alphaNumChar)

rws :: [String] -- list of reserved words
rws = ["<--","epsilon","!", "*", "start:"]

identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
  where
    p       = (:) <$> letterChar <*> many (alphaNumChar <|> char '-')
    check x = if x `elem` rws
                then fail $ "keyword " ++ show x ++ " cannot be an identifier"
                else return x


chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 p op 
  = do{ x <- p; rest x }
    where
      rest x    = do{ f <- op
                    ; y <- p
                    ; rest (f x y)
                    } <|> return x


chainr1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 p op        
  = scan
    where
      scan      = do{ x <- p; rest x }
      rest x    = do{ f <- op
                    ; y <- scan
                    ; return (f x y)
                    } <|> return x
