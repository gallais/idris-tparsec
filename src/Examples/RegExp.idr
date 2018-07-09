module Examples.RegExp 

import Data.NEList
import TParsec
import TParsec.Running

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

Eq TOK where
  (==) OPEN     OPEN     = True
  (==) NOPEN    NOPEN    = True
  (==) CLOSE    CLOSE    = True
  (==) STAR     STAR     = True
  (==) ANY      ANY      = True
  (==) DOTS     DOTS     = True
  (==) OR       OR       = True
  (==) LPAR     LPAR     = True
  (==) RPAR     RPAR     = True
  (==) (CHAR c) (CHAR d) = c == d
  (==) _        _        = False

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

SizedInput TOK (SizedList TOK) where
  sizedInput = MkSizedList    

Params : Parameters
Params = unInstr TOK (SizedList TOK)

Parser' : Type -> Nat -> Type
Parser' = Parser Params Maybe

-- workarounds for #4504
exactTOK : TOK -> All (Parser' TOK)   
exactTOK = exact

maybeTOK : (TOK -> Maybe Char) -> All (Parser' Char)   
maybeTOK = maybeTok

range : All (Parser' Range)
range = map (uncurry $ \c => maybe (Single c) (Interval c))
            (maybeTOK isCHAR `andopt` (exactTOK DOTS `rand` maybeTOK isCHAR))

regexp : All (Parser' RegExp)
regexp = fix _ $ \rec => 
           let parens   = between (exactTOK LPAR) (exactTOK RPAR)
               parensm  = betweenm (exactTOK LPAR) (exactTOK RPAR)
               ranges   = Combinators.app ((cmap Bracket (exactTOK OPEN)) `alt` (cmap (BracketNot . NEList.toList) (exactTOK NOPEN)))
                              ((nelist range) `land` (exact CLOSE))
               literals = Combinators.map (foldrf (Conj . literal) literal) (nelist (maybeTOK isCHAR))
               base     = alts [ranges, cmap (BracketNot []) (exactTOK ANY), literals, parens rec]
               star     = map (\(r,m) => maybe r (const $ Star r) m) (base `andopt` exact STAR)
               disj     = chainr1 star (Disj `cmap` exactTOK OR)
              in 
           map (foldr1 Conj) (nelist (parensm disj))

---- test

TestT : Type 
TestT = parse "[a..zA..Z0..9-]*\\.agd(a|ai)" regexp

test : TestT
test = MkSingleton (Conj (Star (Bracket (MkNEList (Interval 'a' 'z') [Interval 'A' 'Z', Interval '0' '9', Single '-']))) 
                         (Conj (Conj (Bracket (MkNEList (Single '.') [])) (Conj (Bracket (MkNEList (Single 'a') [])) (Conj (Bracket (MkNEList (Single 'g') [])) (Bracket (MkNEList (Single 'd') []))))) 
                               (Disj (Bracket (MkNEList (Single 'a') [])) (Conj (Bracket (MkNEList (Single 'a') [])) (Bracket (MkNEList (Single 'i') []))))))