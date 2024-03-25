{
module PEGParser where

import PEGLexer hiding (lexer)
import ParserExpression 
}

%name parser grammar
%tokentype { Token }
%error { parseError }
%monad { Alex } { >>= } { pure }
%lexer { lexer } { TEOF }
%expect 0


%token 
  '('       {TLParen}
  ')'       {TRParen}
  '/'       {TChoice}
  '*'       {TStar}
  ';'       {TSemi}
  '!'       {TNot}
  '-->'     {TArrow}
  '@start:' {TStart}
  var       {TVar _}
  string    {TSym _}

%right '/'
%nonassoc '*'
%left NOT

%%

many_rev(p)
  :               { [] }
  | many_rev(p) p { $2 : $1 }

many(p)
  : many_rev(p) { reverse $1 }


grammar :: {Grammar}
        :  rules '@start:' expr { Grammar $1 $3 }

rules :: {[(String, Expr)]}
      : many(rule) {$1}

rule :: {(String,Expr)}
     : var '-->' expr ';' {(var2Str $1, $3)}


expr :: {Expr}
     : expr '/' term      {$1 :/: $3}
     | term               {$1}

term :: {Expr}
     : term  nfactor       {$1 :@: $2}
     | nfactor             {$1}

nfactor :: {Expr}
        : '!' nfactor      {Not $2}
        | factor           {$1}

factor :: {Expr}
       : factor '*'        {Star $1}
       | atom              {$1}

atom :: {Expr}
     : string              {mkString $1} 
     | var                 {NT (var2Str $1)}
     | '(' expr ')'        {$2}


{
parseError :: Token -> Alex a
parseError _ = do
  (AlexPn _ line column, _, _, _) <- alexGetInput
  alexError $ "Parse error at line " <> show line <> ", column " <> show column

lexer :: (Token -> Alex a) -> Alex a
lexer = (=<< alexMonadScan)

var2Str :: Token -> String 
var2Str (TVar s) = s 
var2Str _ = error "Impossible! var2Str"

mkString :: Token -> Expr 
mkString (TSym s@(_ : _)) = foldr1 (:@:) $ map Chr s
mkString _ = error "Impossible! mkString"

parseGrammar :: String -> Either String Grammar
parseGrammar s = runAlex s parser

testParser :: FilePath -> IO ()
testParser path 
  = do 
      content <- readFile path 
      print $ parseGrammar content
}
