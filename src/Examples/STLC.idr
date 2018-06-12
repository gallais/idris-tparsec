module Examples.STLC

import TParsec
import TParsec.Running
import TParsec.NEList

%default total

-- Introduction
-------------------------------------------------------------------------------

-- Our goal here is to parse raw terms of a Simply-Typed Lambda-Calculus.
-- We start with the grammar of the types (T) our language covers. As usual
-- the arrow constructor associates to the right which we represent by having
-- a left-nested type (LT) to the left of the arrow constructor. This guarantees
-- the grammar is unambiguous.

-- T := LT          -- base case (LT lets the user insert spurious parentheses)
--    | LT -> T     -- arrow type

-- LT := '<alpha>+  -- base type: a tick followed by a string of letters
--     | (T)        -- left-nested type thanks to parentheses

-- Our language will be presented in a bidirectional fashion. That is: we
-- will distinguish between introduction (I) rules and elimination (E)
-- rules. Here is the grammar we will be using:

-- I := \ x . I     -- lambda abstraction
--    | E           -- eliminations embed into introductions

-- E := x           -- variable case
--    | E I         -- function application
--    | (I : T)     -- cut rule: using an introduction as an elimination at a given type


-- We start by declaring a type alias for the specific type of parser
-- we are going to use. We could stick to the most general type until
-- the very end but we choose not to in this example (see e.g. the
-- Arithmetic example for a most-general-type approach).

Parser' : Type -> Nat -> Type
Parser' = Parser (SizedList Char) Char Maybe

-- Parsing Types
-------------------------------------------------------------------------------

-- We start with an inductive definition corresponding to the grammar (T) of
-- types. And then introduce a parser `type` for `TYPE`.

data TYPE : Type where
  K   : String -> TYPE
  ARR : TYPE -> TYPE -> TYPE

type : All (Parser' TYPE)
type =

  -- The value `type` is built as a fixpoint. We can use the parser `rec` bound
  -- here to perform recursive calls (i.e. to parse substructures).
  fix (Parser' TYPE) $ \ rec =>

  -- We start by writing the parser for LT. It uses various combinators from
  -- TParsec.Combinators:
  -- * `alt` takes the union of two grammars
  -- * `map f p` runs the parser `p` and modifies the returned value with `f`
  -- * `rand p q` (right and) runs `p` then `q` and returns the value of `q`
  -- * `char c` matches exaclty the character `c`
  -- * `alphas` returns a non-empty string of letters
  -- * `parens p` matches an opening parenthesis, runs `p`, matches a closing
  --   parenthesis and returns the value of `p`.

  -- Remenbering that `K` wraps a string into a TYPE this literally gives us:
  -- LT = '<alpha>+ | (T)

    let lt = alt (map K (rand (char '\'') alphas)) (parens rec) in

  -- We can then move on to matching the symbol "->" for an arrow type. Here is
  -- a description of the new combinators we use:
  -- * `cmap v p` runs the parser `p` and returns the constant value `v`
  -- * `withSpaces p` strips spaces before and after running `p`
  -- * `string s` recognizes exactly the string s

  -- So `arr` recognizes exactly "->" (potentially with spaces around) and
  -- returns the function `ARR` of type `TYPE -> TYPE -> TYPE`.
    let arr = cmap ARR (withSpaces (string "->")) in


  -- Finally, we put everything together by using `chainr1`. `chainr1 elt cons`
  -- parses right-nested lists of the form `elt cons (elt cons (...))` with at
  -- least one `elt`.

  -- Remembering the part of the grammar `T := LT | LT -> T`, we see that this
  -- is the ideal candidate for us where `elt` is `lt` and `cons` is `arr`.

    chainr1 lt arr

-- An example: We check that the parser succeeds on "'a -> ('b -> 'c) -> 'd"
-- `parse str p` is defined in `TParsec.Running`. It runs the parser `p` on
-- the String `str` and if that succeeds with value `v`, it demands that the
-- give a proof of `Singleton v`. The only such proof is `MkSingleton v`.

Test : Type
Test = parse {tok = Char} {mn = Maybe} "'a -> ('b -> 'c) -> 'd" type

test : Test
test = MkSingleton (ARR (K "a") (ARR (ARR (K "b") (K "c")) (K "d")))

-- Parsing STLC
-------------------------------------------------------------------------------

-- We start by giving an inductive definition corresponding to our grammar.
-- We have:
-- * values (Val) corresponding to our introduction forms
-- * neutrals (Neu) corresponding to our elimination forms

mutual

  data Val : Type where
    Lam : String -> Val -> Val
    Emb : Neu -> Val

  data Neu : Type where
    Var : String -> Neu
    Cut : Val -> TYPE -> Neu
    App : Neu -> Val -> Neu

-- Because `Emb` embeds `Neu` into `Val` and `Cut` embeds `Val` into `Neu`
-- we can't write one parser independently of the other: both need to be
-- defined at the same time.
-- We introduce ̀`Language` as a record packing a parser for each one of
-- these and we will construct all of `All Language` as a big fixpoint.

record Language (n : Nat) where
  constructor MkLanguage
  val : Parser' Val n
  neu : Parser' Neu n

-- Instead of giving one big definitions as in `Examples.Arithmetic`, we
-- introduce intermediate definitions to slowly build up all the components
-- we need.

-- NB: Most of the definitions will be parametrised by a value of type
-- `Box (Parser' Val)` which we will call `rec`. It will correspond to the
-- recursive call introduced by the use of `fix`. To guarantee totality we
-- can give `fix` the type `(A -> A) -> A` but rather a more limited type
-- ̀ All (Box A :-> A) -> All A` for any family `A : Nat -> Type`.
-- Some parser combinators can take `Box`ed values and other can't depending
-- on whether they guarantee that a performing a recursive call will be safe.
-- Checking the types in `TParsec.Combinators` is helpful.


-- Variables are nothing but non-empty strings.

var : All (Parser' String)
var = alphas

-- Remember that `Cut` corresponds to the `(I : T)` case in the grammar
-- The easy bits first: we use `rand (withSpaces (char ':')) type` to
-- parse the ` : T` part; `parens p` matches the opening & closing parentheses
-- we expect.
-- We use `adjust rec p` to run `rec` then `p` and return the pair of results

cut : All (Box (Parser' Val) :-> Parser' (Pair Val TYPE))
cut rec = parens (adjust rec (rand (withSpaces (char ':')) type)) where

  -- The definition of `adjust` needs quite a bit of explaining.
  -- As we've explained, to guarantee totality the recursive type is wrapped
  -- in a `Box`. We can't just use ̀`and` on `rec` and `rand (...) type` to
  -- grab a value & a type and return both because `and` takes as its first
  -- argument a `Parser A` and not a `Box (Parser A)`.

  -- Luckily for us `TParsec.Induction` defines a way to apply a function
  -- under a `Box`. Or even under two `Box`es: `map2` takes a function of
  -- type `All (A :-> B :-> C)` and returns `All (Box A :-> Box B :-> Box C)`.

  -- The second piece of the puzzle is the fact that `Parser' A` embeds
  -- into `Box (Parser' A)`. And because we've declared this as an implicit
  -- conversion rule we don't have to mention it explicitly here.

  -- Hence:

  adjust : All (Box (Parser' s) :-> Parser' t :-> Box (Parser' (Pair s t)))
  adjust {s} {t} p q =
    Induction.map2 {a=Parser' s} {b=Parser' t} (\ p, q => Combinators.and p q) p q

-- We now know how to parse variables and cuts. We can explain how to parse
-- neutral terms. Remember that `E := x | E I | (I : T)`. We can see that the
-- only recursive call to `E` is in the application case. That is this grammar
-- is equivalent to `E := B | E I` where `B := x | (I : T)`.
-- In other words: we have a left-nested list of applications ending with either
-- a variable or a cut.

-- * `hchainl base cons arg` parses left-nested lists of the shape:
--   `((base cons arg) cons arg) cons arg`
-- * `spaces` parses a non-empty number of spaces.

-- Hence the following definition of `neu`:

neu : All (Box (Parser' Val) :-> Parser' Neu)
neu rec = hchainl (alt (map Var var) (map (uncurry Cut) (cut rec))) (cmap App spaces) rec

-- We can now move on to values. Lambda-abstraction in particular.
-- Remember that lambda-abstractions are of the shape `\ x . I`.

-- The main combinators we use here are:
-- * `rand p q` (right and) runs `p` then `q`; only returns the value produced by `q`
-- * `andm p q` (and maybe) runs `p` then `q` but `q` is allowed to fail

lam : All (Box (Parser' Val) :-> Parser' (Pair String Val))
lam rec = rand (char '\\') (and (withSpaces var) (rand (andm (char '.') spaces) rec))

-- Given that parsing `Emb` is trivial (neutrals silently embed into values so we
-- don't have to match anything), the parser for values is the simple union of the
-- one for lambda-abstraction and the one for neutrals:

val : All (Box (Parser' Val) :-> Parser' Val)
val rec = alt (map (uncurry Lam) (lam rec)) (map Emb (neu rec))

-- Finally we can put it all together. We use `Induction.map` to extract from
-- `Box Language` the `Box (Parser' Val)` we are interested in and use `val`
-- and `neu` defined above.

language : All Language
language = fix Language $ \ rec =>
  let ihv = Induction.map {a=Language} val rec in
  MkLanguage (val ihv) (neu ihv)

-- We can once more write a test by using `parse` and check that our parser indeed
-- produces the right output.

Test2 : Type
Test2 = parse {tok=Char} {mn=Maybe} "\\ x . (\\ y . y : 'a -> 'a) x" (val language)

test2 : Test2
test2 = MkSingleton (Lam "x" (Emb (App (Cut (Lam "y" (Emb (Var "y"))) (ARR (K "a") (K "a")))
                                       (Emb (Var "x")))))
