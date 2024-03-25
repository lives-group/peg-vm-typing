module Compiler where

import ParserExpression
import VM 

-- type to denote jump tables for PEG variables
-- used to patch call instructions with its 
-- correct address

type JumpTable = [(String, Label)] 

-- main compilation function 

compile :: Grammar -> (JumpTable, Code)
compile g 
  = let 
      codeRules = map compileRule (rules g)
      grules = concatMap snd codeRules
      n = length grules + 1
      codeStart = compileExpr (start g) ++ [IJmp (Pos n)]
      table' = mkJumpTable (length codeStart) codeRules 
      instrs = codeStart ++ grules ++ [IEnd] 
    in (table', patchJumps table' instrs)

-- patching jumps, given a jump table 

patchJumps :: JumpTable -> Code -> Code 
patchJumps tbl 
  = map patch 
    where 
      patch (ICall (Hole s))
        = maybe (errMessage s) ICall (lookup s tbl)
      patch x = x 

errMessage :: String -> a 
errMessage s 
  = error $ "Unbound name:" ++ s 

-- creating a jump table 

mkJumpTable :: Int -> [(String, Code)] -> JumpTable 
mkJumpTable = go
      where 
        go _ [] = []
        go curr ((v, cs) : rest) 
          = let n = length cs
            in (v, Pos curr) : go (curr + n) rest  

-- compile a grammar rule 

compileRule :: (String, Expr) -> (String, Code)
compileRule (v,e) = (v, compileExpr e ++ [IReturn])

-- compiling a parsing expression.

compileExpr :: Expr -> Code 
compileExpr (Chr c) = [IChr c]
compileExpr (NT v)  = [ICall $ Hole v]
compileExpr (e1 :@: e2) 
  = compileExpr e1 ++ compileExpr e2
compileExpr (e1 :/: e2)
  = let 
      code1 = compileExpr e1 
      code2 = compileExpr e2 
      n1 = length code1 
      n2 = length code2
      i1 = IChoice (Pos (n1 + 1))
      i2 = ICommit (Pos (n2 + 1))
    in i1 : code1 ++ i2 : code2
compileExpr (Star e1)
  = let 
      code1 = compileExpr e1 
      n1 = length code1 
      i1 = IChoice (Pos (n1 + 2))
      i2 = ICommit (Pos (- (n1  + 1)))
    in i1 : code1 ++ [i2]
compileExpr (Not e1)
  = let 
      code1 = compileExpr e1 
      n1 = length code1 
      i1 = IChoice (Pos (n1 + 2))
    in i1 : code1 ++ [IFail]

-- test :: IO ()
-- test = do 
--   str <- readFile "./test/Example1.peg"
--   let g = parser str
--   case g of 
--     Left err -> putStrLn err
--     Right g' -> do 
--       let (table', codes) = compile g'
--           cs = zip [0 :: Int ..] codes 
--           s = unlines $ map (\ (n,c) -> show n <> " : " <> show c) cs
--       print table' 
--       writeFile "./test/Example1.vm" s
--       
