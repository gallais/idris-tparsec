module Examples.Parentheses 

import Relation.Subset -- for repl
import TParsec
import TParsec.Running

%default total

-- Well-parenthesised string
data PAR = LPAR | RPAR | LCUR | RCUR | LSQU | RSQU

Eq PAR where
  (==) LPAR LPAR = True
  (==) RPAR RPAR = True
  (==) LCUR LCUR = True
  (==) RCUR RCUR = True
  (==) LSQU LSQU = True
  (==) RSQU RSQU = True
  (==) _    _    = False
    
Tokenizer PAR where
  tokenize = foldr ((++) . toPAR) [] . unpack
    where
    toPAR : Char -> List PAR
    toPAR '(' = [LPAR]
    toPAR ')' = [RPAR]
    toPAR '{' = [LCUR]
    toPAR '}' = [RCUR]
    toPAR '[' = [LSQU]
    toPAR ']' = [RSQU]
    toPAR _ = [] -- ignoring other characters as noise

Params : Parameters
Params = unInstr PAR (SizedList PAR)

Parser' : Type -> Nat -> Type
Parser' = Parser Params Maybe

PAR' : All (Parser' ())
PAR' = fix (Parser' ()) $ \rec => 
  let lRrR = \ p, q => cmap () ((exact p `andm` rec) `land` (exact q `andm` rec))
  in
         alts [ lRrR LPAR RPAR
              , lRrR LCUR RCUR
              , lRrR LSQU RSQU
              ]

---- test

--test : parse "hel[{(lo({((wor))ld})wan)t}som{e()[n]o}i(s)e]?" PAR'
--test = MkSingleton ()
