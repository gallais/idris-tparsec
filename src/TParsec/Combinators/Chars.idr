module TParsec.Combinators.Chars

import Data.List
import Relation.Indexed
import Relation.Subset
import Induction.Nat
import Data.Inspect
import Data.List1
import TParsec.Types
import TParsec.Combinators
import TParsec.Combinators.Numbers

%default total

public export
char : {p : Parameters mn} ->
       (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
       Char -> All (Parser mn p (Tok p))
char = exact . into

public export
anyCharBut : {p : Parameters mn} ->
             (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
             Char -> All (Parser mn p (Tok p))
anyCharBut = anyTokenBut . into

public export
string : {p : Parameters mn} ->
         (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
         (t : String) -> {auto pr : NonEmpty (unpack t)} ->
         All (Parser mn p String)
string @{cstr} @{pr} t with (unpack t)
  string @{cstr} @{pr} t | [] = absurd pr
  string @{cstr} @{pr} t | (x :: xs) =
    cmap t $ ands $ map (\c => char c) (x ::: xs)

public export
space : {p : Parameters mn} ->
        (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
        All (Parser mn p (Tok p))
space = anyOf (into <$> unpack " \t\n")

public export
spaces : {p : Parameters mn} ->
         (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
         All (Parser mn p (List1 (Tok p)))
spaces = list1 space

public export
parens : {p : Parameters mn} ->
         (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
         All (Box (Parser mn p a) :-> Parser mn p a)
parens = between (char '(') (box $ char ')')

public export
parensopt : {p : Parameters mn} ->
            (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
            All (Parser mn p a :-> Parser mn p a)
parensopt = betweenopt (char '(') (box $ char ')')

public export
withSpaces : {p : Parameters mn} ->
             (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
             All (Parser mn p a :-> Parser mn p a)
withSpaces p = roptand spaces (landopt p (box spaces))

public export
lowerAlpha : {p : Parameters mn} ->
             (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
             All (Parser mn p (Tok p))
lowerAlpha = anyOf (into <$> unpack "abcdefghijklmnopqrstuvwxyz")

public export
upperAlpha : {p : Parameters mn} ->
             (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
             All (Parser mn p (Tok p))
upperAlpha = anyOf (into <$> unpack "ABCDEFGHIJKLMNOPQRSTUVWXYZ")

public export
alpha : {p : Parameters mn} ->
        (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
        All (Parser mn p (Tok p))
alpha = lowerAlpha `alt` upperAlpha

-- TODO define Bijection?
public export
alphas : {p : Parameters mn} ->
         (Alternative mn, Monad mn, Subset Char (Tok p), Subset (Tok p) Char, Eq (Tok p), Inspect (Toks p) (Tok p)) =>
         All (Parser mn p String)
alphas = map (pack . map into . forget) (list1 alpha)

public export
num : {p : Parameters mn} ->
      (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
      All (Parser mn p Nat)
num = decimalDigit

public export
alphanum : {p : Parameters mn} ->
           (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
           All (Parser mn p (Either (Tok p) Nat))
alphanum = Combinators.sum alpha num
