module Examples.Parentheses 

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

Parser' : Type -> Nat -> Type
Parser' = Parser TParsecU (sizedtok PAR)

PAR' : All (Parser' ())
PAR' = fix _ $ \rec => 
  let lRrR = \p, q => cmap () ((exact p `andopt` rec) `land` (exact q `andopt` rec)) in
  alts [ lRrR LPAR RPAR
       , lRrR LCUR RCUR
       , lRrR LSQU RSQU
       ]

---- test

test : parseType "hel[{(lo({((wor))ld})wan)t}som{e()[n]o}i(s)e]?" PAR'
test = MkSingleton ()
