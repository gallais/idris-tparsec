module Examples.Parentheses 

import TParsec
import TParsec.Running

%default total

-- Well-parenthesised string
data PAR = LPAR | RPAR | LCUR | RCUR | LSQU | RSQU

DecEq PAR where
  decEq LPAR LPAR = Yes Refl
  decEq RPAR RPAR = Yes Refl
  decEq LCUR LCUR = Yes Refl
  decEq RCUR RCUR = Yes Refl
  decEq LSQU LSQU = Yes Refl
  decEq RSQU RSQU = Yes Refl
  decEq _    _    = No $ really_believe_me ()
    
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
Parser' = Parser (SizedList PAR) PAR Maybe

PAR' : All (Parser' ())
PAR' = fix _ $ \rec =>
         alts [ cmap () ((exact LPAR `andm` rec) `land` (exact RPAR `andm` rec))
              , cmap () ((exact LCUR `andm` rec) `land` (exact RCUR `andm` rec))
              , cmap () ((exact LSQU `andm` rec) `land` (exact RSQU `andm` rec))
              ]

---- test

test : parse "hel[{(lo({((wor))ld})wan)t}som{e()[n]o}i(s)e]?" PAR'
test = MkSingleton ()