{
module PEGLexer where

import Control.Monad
import GHC.Base
}

%wrapper "monadUserState"

$digit = [0-9]
$alpha = [a-zA-Z]
$symbol = [$alpha $digit]
@identifier = $alpha [ $alpha $digit ]*
@string = \" [ $symbol ]* \"

tokens :- 
  <0>         $white                         ; 
  <0>         "("                            {\ _ _ -> return TLParen}
  <0>         ")"                            {\ _ _ -> return TRParen}
  <0>         @identifier                    {tokId}
  <0>         "*"                            {\ _ _ -> return TStar}
  <0>         "/"                            {\ _ _ -> return TChoice}
  <0>         "!"                            {\ _ _ -> return TNot}
  <0>         "-->"                          {\ _ _ -> return TArrow}
  <0>         ";"                            {\ _ _ -> return TSemi}
  <0>         "@start:"                      {\ _ _ -> return TStart}
  <0>         \"                             {enterString `andBegin` string}
  <string>    \"                             {exitString `andBegin` 0}
  <string>    \\\\                           {emit '\\'}
  <string>    \\\"                           {emit '"'}
  <string>    \\n                            {emit '\n'}
  <string>    \\t                            {emit '\t'}
  <string>    .                              {emitCurrent}

  
{
data Token 
  = TVar String 
  | TSym String 
  | TLParen
  | TRParen
  | TStar
  | TChoice 
  | TNot 
  | TArrow
  | TSemi
  | TStart
  | TEOF 
  deriving (Eq, Show)

data AlexUserState = AlexUserState
  { 
    strStart :: AlexPosn
  , strBuffer :: [Char]
  }

alexInitUserState :: AlexUserState
alexInitUserState = AlexUserState
  { 
    strStart = AlexPn 0 0 0
  , strBuffer = []
  }

get :: Alex AlexUserState
get = Alex $ \s -> Right (s, alex_ust s)

put :: AlexUserState -> Alex ()
put s' = Alex $ \s -> Right (s{alex_ust = s'}, ())

modify :: (AlexUserState -> AlexUserState) -> Alex ()
modify f = Alex $ \s -> Right (s{alex_ust = f (alex_ust s)}, ())

alexEOF :: Alex Token
alexEOF = do
  (pos, _, _, _) <- alexGetInput
  startCode <- alexGetStartCode
  when (startCode == string) $
    alexError "Error: unclosed string"
  pure TEOF


enterString, exitString :: AlexAction Token
enterString inp@(pos, _, _, _) len = do
  modify $ \s -> s{strStart = pos, strBuffer = strBuffer s}
  skip inp len
exitString inp@(pos, _, _, _) len = do
  s <- get
  put s{strStart = AlexPn 0 0 0, strBuffer = []}
  pure (TSym $ strBuffer s)

emit :: Char -> AlexAction Token
emit c inp@(_, _, _, str) len = do
  modify $ \s -> s{strBuffer = c : strBuffer s}
  skip inp len

emitCurrent :: AlexAction Token
emitCurrent inp@(_, _, _, str) len = do
  modify $ \s -> s{strBuffer = head str : strBuffer s}
  skip inp len

tokId :: AlexAction Token
tokId inp@(_, _, _, str) len =
  pure $ TVar $ take len str


w2c :: Word8 -> Char 
w2c = unsafeChr . fromIntegral 

lexer :: String -> Either String [Token]
lexer input = runAlex input go
  where
    go = do
      output <- alexMonadScan
      if output == TEOF
        then pure []
        else (output :) <$> go

testLexer :: FilePath -> IO ()
testLexer path 
  = do 
      content <- readFile path 
      print $ lexer content 
}
