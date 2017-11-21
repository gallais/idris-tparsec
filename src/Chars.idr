module Chars

import Indexed
import Induction
import Inspect
import Combinators
import NEList
import Numbers

%default total
%access public export

char : (Inspect toks Char, Alternative mn, Monad mn) =>
       Char -> All (Parser toks Char mn Char)
char = exact

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

alpha : (Inspect toks Char, Alternative mn, Monad mn) =>
        All (Parser toks Char mn Char)
alpha = anyOf (unpack "abcdefghijklmnopqrstuvwxyz")


num : (Inspect toks Char, Alternative mn, Monad mn) =>
      All (Parser toks Char mn Nat)
num = decimalDigit

alphanum : (Inspect toks Char, Alternative mn, Monad mn) =>
           All (Parser toks Char mn (Either Char Nat))
alphanum = sum alpha num
