module Examples.RegExp 

import TParsec
import TParsec.Running
import TParsec.NEList

%default total
    
data Range : Type where
  Single : Char -> Range
  Interval : (lb, ub : Char) -> Range

Show Range where
  show (Single c) = "singleton " ++ show c
  show (Interval lb ub) = "interval " ++ show lb ++ " " ++ show ub

data RegExp : Type where
  Eps        : RegExp
  Bracket    : (as : NEList Range) -> RegExp
  BracketNot : (as : List Range) -> RegExp
  Disj       : (e1, e2 : RegExp) -> RegExp
  Conj       : (e1, e2 : RegExp) -> RegExp
  Star       : (e : RegExp) -> RegExp

Show RegExp where
  show Eps = "eps"  
  show (Bracket as) = "`" ++ show as
  show (BracketNot as) = "`^" ++ show as
  show (Disj e1 e2) = "(" ++ show e1 ++ " || " ++ show e2 ++ ")"
  show (Conj e1 e2) = "(" ++ show e1 ++ " x " ++ show e2 ++ ")"
  show (Star e) = show e ++ "*"

literal : Char -> RegExp
literal = Bracket . singleton . Single

data TOK : Type where
  OPEN  : TOK
  NOPEN : TOK
  CLOSE : TOK
  ANY   : TOK
  STAR  : TOK
  DOTS  : TOK
  OR    : TOK
  LPAR  : TOK
  RPAR  : TOK
  CHAR  : Char -> TOK

isCHAR : TOK -> Maybe Char
isCHAR (CHAR c) = Just c
isCHAR _        = Nothing

DecEq TOK where
  decEq OPEN     OPEN     = Yes Refl
  decEq NOPEN    NOPEN    = Yes Refl
  decEq CLOSE    CLOSE    = Yes Refl
  decEq STAR     STAR     = Yes Refl
  decEq ANY      ANY      = Yes Refl
  decEq DOTS     DOTS     = Yes Refl
  decEq OR       OR       = Yes Refl
  decEq LPAR     LPAR     = Yes Refl
  decEq RPAR     RPAR     = Yes Refl
  decEq (CHAR c) (CHAR d) with (decEq c d)
    | Yes eq = Yes (cong eq)
    | No neq = No $ neq . aux
      where 
      aux : CHAR a = CHAR b -> a = b
      aux Refl = Refl
  decEq _        _        = No $ really_believe_me ()

Tokenizer TOK where
  tokenize = toTOKs . unpack
    where
    toTOKs : List Char -> List TOK
    toTOKs []                 = []
    toTOKs ('\\' :: c :: cs)  = CHAR c :: toTOKs cs
    toTOKs ('[' :: '^' :: cs) = NOPEN  :: toTOKs cs
    toTOKs ('[' :: cs)        = OPEN   :: toTOKs cs
    toTOKs (']' :: cs)        = CLOSE  :: toTOKs cs
    toTOKs ('.' :: '.' :: cs) = DOTS   :: toTOKs cs
    toTOKs ('.' :: cs)        = ANY    :: toTOKs cs
    toTOKs ('(' :: cs)        = LPAR   :: toTOKs cs
    toTOKs (')' :: cs)        = RPAR   :: toTOKs cs
    toTOKs ('*' :: cs)        = STAR   :: toTOKs cs
    toTOKs ('|' :: cs)        = OR     :: toTOKs cs
    toTOKs (c :: cs)          = CHAR c :: toTOKs cs

Parser' : Type -> Nat -> Type
Parser' = Parser (SizedList TOK) TOK Maybe

range : All (Parser' Range)
range = map (uncurry $ \c => maybe (Single c) (Interval c))
            (maybeTok isCHAR `andm` (exact DOTS `rand` maybeTok isCHAR))

regexp : All (Parser' RegExp)
regexp = fix _ $ \rec => 
           let parens   = between (exact LPAR) (exact RPAR)
               parensm  = betweenm (exact LPAR) (exact RPAR)
               ranges   = app ((cmap Bracket (exact OPEN)) `alt` (cmap (BracketNot . NEList.toList) (exact NOPEN)))
                              ((nelist range) `land` (exact CLOSE))
               literals = map (foldrf (Conj . literal) literal) (nelist (maybeTok isCHAR))
               base     = alts [ranges, cmap (BracketNot []) (exact ANY), literals, parens rec]
               star     = map (\(r,m) => maybe r (const $ Star r) m) (base `andm` exact STAR)
               disj     = chainr1 star (Disj `cmap` exact OR)
              in 
           map (foldr1 Conj) (nelist (parensm disj))

---- test

TestT : Type 
TestT = parse {mn=Maybe} {tok=TOK} "[a..zA..Z0..9-]*\\.agd(a|ai)" regexp

test : TestT
test = MkSingleton (Conj (Star (Bracket (MkNEList (Interval 'a' 'z') [Interval 'A' 'Z', Interval '0' '9', Single '-']))) 
                         (Conj (Conj (Bracket (MkNEList (Single '.') [])) (Conj (Bracket (MkNEList (Single 'a') [])) (Conj (Bracket (MkNEList (Single 'g') [])) (Bracket (MkNEList (Single 'd') []))))) 
                               (Disj (Bracket (MkNEList (Single 'a') [])) (Conj (Bracket (MkNEList (Single 'a') [])) (Bracket (MkNEList (Single 'i') []))))))