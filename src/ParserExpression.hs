module ParserExpression where 


-- basic expression syntax 

data Expr 
  = Chr Char 
  | NT String 
  | Expr :@: Expr 
  | Expr :/: Expr 
  | Star Expr 
  | Not Expr 
  deriving (Eq, Show)

-- definition of the grammars

data Grammar 
  = Grammar {
      rules :: [(String, Expr)]
    , start :: Expr 
    } deriving (Eq, Show)

-- types for parsing expressions 

data Ty 
  = Ty {
      nullable :: Bool 
    , headSet  :: [String]
    }
  | Var Int
  deriving (Eq, Show)

