module PEGTypeInfer where

import Control.Monad.Identity
import Control.Monad.Except 
import Control.Monad.State 
import Data.List (union)
import Data.Maybe
import ParserExpression 
import PEGParser
import System.Process hiding (env)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L


-- top level type inference 

typeInfer :: Grammar -> IO Env 
typeInfer g 
  = case genConstr g of 
      Left err -> error "invalid grammar"
      Right (env,c) -> solveConstr c env 

-- top level constraint solving 

solveConstr :: Constr -> Env -> IO Env 
solveConstr c env 
  = do 
      let script1 = smtScript GetModel env c       
          f (s, (Var n)) = (s, "t" <> show n)
          f (s, _) = (s, "")
          res = map f env 
      writeFile "./Constr.smt" script1
      out <- readProcess "z3" ["./Constr.smt"] ""
      case parse parseModel "" out of
        Left err1 -> error "Type error in input grammar!" 
        Right (Model _ env') -> 
          return [(s,t) | (s,tn) <- res
                        , (tn', t) <- env'
                        , tn == tn']

-- top level constraint generation 

genConstr :: Grammar -> Either Error (Env, Constr)
genConstr g 
  = fst <$> runIdentity (runExceptT (runStateT (genConstrM g) 0)) 


-- definition of the constraint generation monad 

type Error = String 
type Env = [(String,Ty)]
type GenM a = StateT Int (ExceptT Error Identity) a

-- syntax of contraints 

data Constr 
  = Top 
  | Ty :=: Ty
  | CNT String Ty     -- non terminal constraint 
  | Constr :&: Constr 
  | CProd Ty Ty Ty    -- product type constraint 
  | CSum  Ty Ty Ty    -- sum type constraint 
  | CStar Ty Ty       -- star type constraint 
  | CNot  Ty Ty 
  deriving (Eq, Show)

-- free type variables from a type 

fvt :: Ty -> [Int]
fvt (Var n) = [n]
fvt _ = []

-- free type variables from a constraint

fv :: Constr -> [Int]
fv (t1 :=: t2) = fvt t1 `union` fvt t2
fv (CNT _ t) = fvt t
fv (c1 :&: c2) = fv c1 `union` fv c2
fv (CProd t1 t2 t3) = fvt t1 `union` fvt t2 `union` fvt t3
fv (CSum t1 t2 t3) = fvt t1 `union` fvt t2 `union` fvt t3
fv (CStar t1 t2) = fvt t1 `union` fvt t2
fv (CNot t1 t2) = fvt t1 `union` fvt t2
fv _ = []

-- generating constraints 

genConstrM :: Grammar -> GenM (Env, Constr) 
genConstrM (Grammar rs e)
  = do
      env <- buildEnv rs 
      cs <- genConstrRules env rs 
      v  <- fresh 
      c  <- genConstrExpr env e (Var v)
      pure (env, cs :&: c)

buildEnv :: [(String,Expr)] -> GenM Env
buildEnv = mapM go 
    where 
      go s = do 
        n <- fresh 
        pure (fst s, Var n)

-- generating constraints for rules 

genConstrRules :: Env -> [(String, Expr)] -> GenM Constr 
genConstrRules env 
  = foldM step Top 
    where 
      step ac (v, e) 
        = do
            let t = fromJust $ lookup v env 
            c <- genConstrExpr env e t
            pure $ ac :&: c

-- generating constraints for expressions 

genConstrExpr :: Env -> Expr -> Ty -> GenM Constr 
genConstrExpr _ (Chr _) t
  = pure $ t :=: Ty False []
genConstrExpr _ (NT v) t 
  = pure $ CNT v t
genConstrExpr env (e1 :/: e2) t 
  = do 
      n1 <- fresh 
      c1 <- genConstrExpr env e1 (Var n1)
      n2 <- fresh 
      c2 <- genConstrExpr env e2 (Var n2)
      pure $ c1 :&: c2 :&: CSum t (Var n1) (Var n2)
genConstrExpr env (e1 :@: e2) t 
  = do 
      n1 <- fresh 
      c1 <- genConstrExpr env e1 (Var n1)
      n2 <- fresh 
      c2 <- genConstrExpr env e2 (Var n2)
      pure $ c1 :&: c2 :&: CProd t (Var n1) (Var n2)
genConstrExpr env (Star e1) t 
  = do 
      n1 <- fresh 
      c1 <- genConstrExpr env e1 (Var n1)
      pure $ c1 :&: CStar t (Var n1)
genConstrExpr env (Not e1) t 
  = do 
      n1 <- fresh 
      c1 <- genConstrExpr env e1 (Var n1)
      pure $ c1 :&: CNot t (Var n1)

-- generating a new variable 

fresh :: GenM Int 
fresh = do 
  n <- get 
  put (n + 1)
  pure n

-- generate the proof script for the SMT solver 

data Mode = Check | GetModel deriving (Eq, Show) 

smtScript :: Mode -> Env -> Constr -> String 
smtScript m env c = unlines [nt, header, vars, asserts, ender m]
  where
    ender Check = "(check-sat)"
    ender _     = "(check-sat)\n(get-model)"
    
    asserts = unlines $ map passet $ core c

    nt = unwords ["(declare-datatypes () ((NT", nonTerm,")))"]

    nonTerm = if null env then "bla" else unwords $ map fst env 

    passet (t1 :=: t2) = unwords ["(assert (=", pty t1, pty t2, "))"]
    passet (CNT v t) = let t1 = fromJust $ lookup v env 
                        in unwords [ "(assert (not (member"
                                   , v 
                                   , pty t1
                                   , ")))\n"
                                   , "(assert (="
                                   , pty t 
                                   , "(mk-type (is-null"
                                   , pty t1 
                                   , ") (union (singleton"
                                   , v 
                                   , ") (head-set "
                                   , pty t1
                                   , ")))))"]
    passet (CProd t1 t2 t3) = unwords [ "(assert (=", pty t1
                                      , "(prod"
                                      , pty t2
                                      , pty t3
                                      , ")))"]
    passet (CSum t1 t2 t3) = unwords [ "(assert (="
                                     , pty t1
                                     , "(sum"
                                     , pty t2
                                     , pty t3
                                     , ")))"
                                     ]
    passet (CNot t1 t2) = unwords [ "(assert (="
                                  , pty t1
                                  , "(neg"
                                  , pty t2
                                  , ")))"
                                  ]
    passet (CStar t1 t2) =  unwords [ "(assert (="
                                    , pty t1
                                    , "(star"
                                    , pty t2
                                    , ")))\n"
                                    , "(assert (not (is-null", pty t2,")))"
                                    ]
    passet _ = ""
 
    pty (Var n) = "t" <> show n 
    pty (Ty b _) = unwords ["(mk-type", pbool b, "empty)"]

    pbool True = "true"
    pbool _ = "false"
    
    vars = unlines $ map mkVar (fv c)

    mkVar n = unwords [ "(declare-const"
                      , "t" <> show n
                      , "Type)"
                      ]
    header = unlines [ "(declare-datatypes () ((Type"
                     , "  (mk-type (is-null Bool) (head-set (Set NT))))))"
                     , "(define-fun empty () (Set NT)"
                     , "  ((as const (Set NT)) false))"
                     , "(define-fun singleton ((a NT)) (Set NT)"
                     , "  (store empty a true))"
                     , "(define-fun union ((a (Set NT)) (b (Set NT))) (Set NT)"
                     , "  ((_ map or) a b))"
                     , "(define-fun imp ((b Bool) (s (Set NT))) (Set NT)"
                     , "  (ite b s empty))"
                     , "(define-fun prod ((a Type) (b Type)) (Type)"
                     , "  (mk-type (and (is-null a) (is-null b))"
                     , "    (union (head-set a) (imp (is-null a) (head-set b)))))"
                     , "(define-fun sum ((a Type) (b Type)) (Type)"
                     , "  (mk-type (or (is-null a)"
                     , "               (is-null b))"
                     , "           (union (head-set a)"
                     , "                  (head-set b))))"
                     , "(define-fun star ((a Type)) (Type)"
                     , "  (mk-type true"
                     , "           (head-set a)))"
                     , "(define-fun neg ((a Type)) (Type)"
                     , "  (mk-type true"
                     , "           (head-set a)))"
                     , "(define-fun member ((a NT) (t Type)) (Bool)"
                     , "  (select (head-set t) a))"
                     ]

-- getting the core constraints 

core :: Constr -> [Constr]
core Top = []
core (c1 :&: c2) = core c1 ++ core c2 
core c = [c] 

-- model parser 

data Result = SAT | UNSAT deriving (Eq, Show)

data Model = Model Result [(String, Ty)]
             deriving (Eq, Show)

parseModel :: Parser Model 
parseModel = Model <$> parseResult <*> parseDefList  

parseResult :: Parser Result 
parseResult 
  = (SAT <$ symbol "sat") <|> 
    (UNSAT <$ symbol "unsat")
        
parseDefList :: Parser [(String,Ty)]
parseDefList 
  = concat <$> (parens $ many parseDef)

parseDef :: Parser [(String, Ty)]
parseDef 
  = parens $ do {
      _ <- symbol "define-fun" ; 
      s <- identifier ; 
      params ; 
      parseAType ; 
      parseBody s
    } 

params :: Parser ()
params 
  = parens argList 

argList :: Parser ()
argList = () <$ many arg 

arg :: Parser String
arg = parens (identifier <* parseAType)

parseAType :: Parser String 
parseAType = symbol "Type" <|> symbol "(Set NT)"

parseBody :: String -> Parser [(String, Ty)]
parseBody s 
  = (map (\ x -> (s,x)) . catMaybes) <$> many parseOneType

parseOneType :: Parser (Maybe Ty)
parseOneType 
  = try (Nothing <$ (parens $ symbol "(as const (Set NT)) false")) <|>
    (Just <$> parseConstructor)

parseConstructor :: Parser Ty
parseConstructor 
  =  parens $ do { 
        _ <- symbol "mk-type" ;
        b <- parseBool ;
        ts <- parseHeadSet ; 
        pure (Ty b ts)
     }

parseHeadSet :: Parser [String]
parseHeadSet 
  = try ([] <$ parseEmptySet) <|>
    try parseSingleton        <|>
    parseUnion 

parseEmptySet :: Parser () 
parseEmptySet
  = () <$ symbol "((as const (Set NT)) false)"

parseSingleton :: Parser [String]
parseSingleton 
  = (parens $ do {
      _ <- symbol "store" ; 
      ts <- parseHeadSet ; 
      t <- identifier ; 
      _ <- symbol "true" ;
      return (t : ts)
     }) <?> "singleton"

parseUnion :: Parser [String]
parseUnion 
  = (parens $ do {
      unionToken ;
      concat <$> many parseHeadSet
     }) <?> "union"

parseBool :: Parser Bool 
parseBool = True <$ symbol "true" <|> 
            False <$ symbol "false"

unionToken :: Parser ()
unionToken 
  = () <$ symbol "(_ map (or (Bool Bool) Bool))"

test = do 
  str <- readFile "./test/Example1.peg"
  let g = parser str
  case g of 
    Left err -> putStrLn err
    Right g' -> do 
      env <- typeInfer g' 
      mapM_ print env
