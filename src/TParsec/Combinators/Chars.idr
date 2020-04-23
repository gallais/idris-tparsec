module TParsec.Combinators.Chars

import Relation.Indexed
import Relation.Subset
import Induction.Nat
import Data.Inspect
import Data.NEList
import TParsec.Types
import TParsec.Combinators
import TParsec.Combinators.Numbers

%default total
%access public export

char : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
       Char -> All (Parser mn p (Tok p))
char = exact . into

anyCharBut : ( Alternative mn, Monad mn
             , Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)
             ) => Char -> All (Parser mn p (Tok p))
anyCharBut = anyTokenBut . into

noneOfChars : ( Alternative mn, Monad mn
              , Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)
              ) => List Char -> All (Parser mn p (Tok p))
noneOfChars = noneOf . map into

string : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
         (t : String) -> {auto pr : NonEmpty (unpack t)} ->
         All (Parser mn p String)
string t {pr} with (unpack t)
  | []        = absurd pr
  | (x :: xs) = cmap t (ands (map (\c => char c) $ MkNEList x xs))

space : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
        All (Parser mn p (Tok p))
space = anyOf (map into $ unpack " \t\n")

spaces : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
         All (Parser mn p (NEList (Tok p)))
spaces = nelist space

parens : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
         All (Box (Parser mn p a) :-> Parser mn p a)
parens = between (char '(') (char ')')

parensopt : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
          All (Parser mn p a :-> Parser mn p a)
parensopt = betweenopt (char '(') (char ')')

withSpaces : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
             All (Parser mn p a :-> Parser mn p a)
withSpaces p = roptand spaces (landopt p spaces)

lowerAlpha : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
             All (Parser mn p (Tok p))
lowerAlpha = anyOf (map into $ unpack "abcdefghijklmnopqrstuvwxyz")

upperAlpha : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
             All (Parser mn p (Tok p))
upperAlpha = anyOf (map into $ unpack "ABCDEFGHIJKLMNOPQRSTUVWXYZ")

alpha : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
        All (Parser mn p (Tok p))
alpha = lowerAlpha `alt` upperAlpha

-- TODO define Bijection?
alphas : (Alternative mn, Monad mn, Subset Char (Tok p), Subset (Tok p) Char, Eq (Tok p), Inspect (Toks p) (Tok p)) =>  
         All (Parser mn p String)
alphas = map (pack . map into . NEList.toList) (nelist alpha)

num : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
      All (Parser mn p Nat)
num = decimalDigit

alphanum : (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
           All (Parser mn p (Either (Tok p) Nat))
alphanum = sum alpha num
