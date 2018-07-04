module TParsec.Chars

import Relation.Indexed
import Relation.Subset
import Induction.Nat
import Data.Inspect
import Data.NEList
import TParsec.Types
import TParsec.Combinators
import TParsec.Instruments
import TParsec.Numbers

%default total
%access public export

char : (Alternative mn, Monad mn, Instrumented p mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
       Char -> All (Parser p mn (Tok p))
char = exact . into

string : (Alternative mn, Monad mn, Instrumented p mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
         (t : String) -> {auto pr : NonEmpty (unpack t)} ->
         All (Parser p mn String)
string t {pr} with (unpack t)
  | []        = absurd pr
  | (x :: xs) = cmap t (ands (map (\c => char c) $ MkNEList x xs))

space : (Alternative mn, Monad mn, Instrumented p mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
        All (Parser p mn (Tok p))
space = anyOf (map into $ unpack " \t\n")

spaces : (Alternative mn, Monad mn, Instrumented p mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
         All (Parser p mn (NEList (Tok p)))
spaces = nelist space

parens : (Alternative mn, Monad mn, Instrumented p mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
         All (Box (Parser p mn a) :-> Parser p mn a)
parens = between (char '(') (char ')')

parensm : (Alternative mn, Monad mn, Instrumented p mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
          All (Parser p mn a :-> Parser p mn a)
parensm = betweenm (char '(') (char ')')

withSpaces : (Alternative mn, Monad mn, Instrumented p mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
             All (Parser p mn a :-> Parser p mn a)
withSpaces p = rmand spaces (landm p spaces)

lowerAlpha : (Alternative mn, Monad mn, Instrumented p mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
             All (Parser p mn (Tok p))
lowerAlpha = anyOf (map into $ unpack "abcdefghijklmnopqrstuvwxyz")

upperAlpha : (Alternative mn, Monad mn, Instrumented p mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
             All (Parser p mn (Tok p))
upperAlpha = anyOf (map into $ unpack "ABCDEFGHIJKLMNOPQRSTUVWXYZ")

alpha : (Alternative mn, Monad mn, Instrumented p mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
        All (Parser p mn (Tok p))
alpha = lowerAlpha `alt` upperAlpha

-- TODO define Bijection?
alphas : (Alternative mn, Monad mn, Instrumented p mn, Subset Char (Tok p), Subset (Tok p) Char, Eq (Tok p), Inspect (Toks p) (Tok p)) =>  
         All (Parser p mn String)
alphas = map (pack . map into . NEList.toList) (nelist alpha)

num : (Alternative mn, Monad mn, Instrumented p mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
      All (Parser p mn Nat)
num = decimalDigit

alphanum : (Alternative mn, Monad mn, Instrumented p mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
           All (Parser p mn (Either (Tok p) Nat))
alphanum = sum alpha num
