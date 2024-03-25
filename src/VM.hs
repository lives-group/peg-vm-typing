module VM where

-- definition of instruction set 

data Label 
  = Hole String 
  | Pos Int 
  deriving (Eq, Show)


data Instr 
  = IChr Char 
  | IJmp Label
  | IChoice Label
  | ICall Label 
  | IReturn 
  | ICommit Label
  | IFail 
  | IEnd 
  deriving (Eq, Show) 

type Code = [Instr]
