module TParsec.Chars

import Relation.Indexed
import Induction.Nat
import Data.Inspect
import Data.NEList
import TParsec.Combinators
import TParsec.Numbers

%default total
%access public export

char : (Inspect toks Char, Alternative mn, Monad mn) =>
       Char -> All (Parser toks Char mn Char)
char = exact

string : (Inspect toks Char, Alternative mn, Monad mn) =>
         (t : String) -> {auto pr : NonEmpty (unpack t)} ->
         All (Parser toks Char mn String)
string t {pr} with (unpack t)
  | []        = absurd pr
  | (x :: xs) = cmap t (ands (map (\ c => char c) $ MkNEList x xs))

space : (Inspect toks Char, Alternative mn, Monad mn) =>
        All (Parser toks Char mn Char)
space = anyOf (unpack " \t\n")

spaces : (Inspect toks Char, Alternative mn, Monad mn) =>
         All (Parser toks Char mn (NEList Char))
spaces = nelist space

parens : (Inspect toks Char, Alternative mn, Monad mn) =>
         All (Box (Parser toks Char mn a) :-> Parser toks Char mn a)
parens = between (char '(') (char ')')

parensm : (Inspect toks Char, Alternative mn, Monad mn) =>
          All (Parser toks Char mn a :-> Parser toks Char mn a)
parensm = betweenm (char '(') (char ')')

withSpaces : (Inspect toks Char, Alternative mn, Monad mn) =>
             All (Parser toks Char mn a :-> Parser toks Char mn a)
withSpaces p = rmand spaces (landm p spaces)

lowerAlpha : (Inspect toks Char, Alternative mn, Monad mn) =>
             All (Parser toks Char mn Char)
lowerAlpha = anyOf (unpack "abcdefghijklmnopqrstuvwxyz")

upperAlpha : (Inspect toks Char, Alternative mn, Monad mn) =>
             All (Parser toks Char mn Char)
upperAlpha = anyOf (unpack "ABCDEFGHIJKLMNOPQRSTUVWXYZ")

alpha : (Inspect toks Char, Alternative mn, Monad mn) =>
        All (Parser toks Char mn Char)
alpha = lowerAlpha `alt` upperAlpha

alphas : (Inspect toks Char, Alternative mn, Monad mn) =>
         All (Parser toks Char mn String)
alphas = map (pack . NEList.toList) (nelist alpha)

num : (Inspect toks Char, Alternative mn, Monad mn) =>
      All (Parser toks Char mn Nat)
num = decimalDigit

alphanum : (Inspect toks Char, Alternative mn, Monad mn) =>
           All (Parser toks Char mn (Either Char Nat))
alphanum = sum alpha num
