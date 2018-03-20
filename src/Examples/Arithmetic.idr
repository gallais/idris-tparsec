module Examples.Arithmetic

-- This module implements a recursive parser for arithmetic expressions
-- involving literals, addition, subtraction, multiplication and division.

-- The grammar of the small language we are considering could be defined
-- as follows (<nat> represents literals in decimal notation):

-- E := T | E + T | E - T
-- T := F | T * F | T / F
-- F := <nat> | (E)

-- One of the key things to observe is the *left nesting* in this grammar:
-- e.g. `E` admits `E + T` as one of its possible matches.

import TParsec
import TParsec.Running

%default total

-- Here we start by introducing a datatype which makes it painfully
-- clear that we have left-nested expressions and that they are
-- stratified into Expr, Term, and Factor.
-- These datatypes are in one-to-one correspondance with the non-terminals
-- of the grammar we presented above.

mutual

 -- `Expr` is `E`
 data Expr : Type where
   EEmb : Term -> Expr
   EAdd : Expr -> Term -> Expr
   ESub : Expr -> Term -> Expr

 -- `Term` is `T`
 data Term : Type where
   TEmb : Factor -> Term
   TMul : Term -> Factor -> Term
   TDiv : Term -> Factor -> Term

 -- `Factor` is `F`
 data Factor : Type where
   FLit : Nat -> Factor
   FEmb : Expr -> Factor

-- Looking back at our grammar:
-- * the rules for `E` involve `T`
-- * the rules for `T` involve `F`
-- * the rules for `F` involve `E`

-- These dependencies mean that we are going to need to define all of the
-- parsers at the same time by mutual induction.

-- So we define a record `Language` which, given a type of tokens `toks`,
-- a monad `mn` and a natural number packs together `Parser`s processing
-- `toks` in the monad `mn` to produce respectively values of type `Expr`,
-- `Term`, and `Factor`.

record Language (toks : Nat -> Type) (mn : Type -> Type) (n : Nat) where
  constructor MkLanguage
  _expr   : Parser toks Char mn Expr n
  _term   : Parser toks Char mn Term n
  _factor : Parser toks Char mn Factor n

-- We are now ready to build a `Language toks mn n` for all `n` by recursion.
-- We have a few constraints which arise directly from the combinators we are
-- going to use.
-- ̀`Inspect toks Char` means that `toks` is essentially a list of `Char`s.
-- In particular, this means that we can make sure that the first character
-- of the input string is a specific `Char` e.g. '+'.

language : (Inspect toks Char, Alternative mn, Monad mn) => All (Language toks mn)
language {toks} {mn} =

  -- The value of type `Language` is build as a fixpoint.
  -- We can use the variable `rec` bound here to perform a recursive call.
  fix (Language toks mn) $ \ rec =>

  -- We start by writing the parsers recognizing basic operations on numbers:
  -- * `alt` is used to take the union of two grammars
  -- * `char c` is used to recognize exactly the character `c`
  -- * `cmap v p` is used to return `v` whener `p` is a successful parse

  -- From these we can see that:
  -- `addop` parses either `+` or `-` and returns the right `Expr` constructor
  let addop  = alt (cmap EAdd (char '+')) (cmap ESub (char '-')) in
  -- `mulop` parses either `*` or `/` and returns the right `Term` constructor
  let mulop  = alt (cmap TMul (char '*')) (cmap TDiv (char '/')) in

  -- We now need to use some new concepts
  -- * `parens p` parses an opening parenthesis, a value thanks to `p` and then
  --   a closing parenthesis. It returns whatever `p` produced.
  -- * `Induction.map f` applies the function `f` to a recusive call. Here it is
  --   used to project the parser for `Expr` out of `Language`.
  -- * `decimalNat` is a parser for decimal numbers defined in `TParsec.Numbers`

  -- `factor` recognizes either an `Expr` in between parentheses or a natural number
  let factor = alt (map FEmb (parens (Induction.map {a = Language _ _} _expr rec)))
                   (map FLit decimalNat) in

  -- We now have all the basic building blocks and can assemble them.

  -- `hchainl base step arg` parses left-nested lists of the form
  -- `((base step arg) step arg) step ...`

  -- Remembering the part of the grammar grammar `T := F | T * F | T / F`
  -- we write the parser for `Term` as:
  -- * a left-nested list of `mulop` (i.e. * and /) and `factor`
  -- * starting with a `factor`.
  let term   = hchainl (map TEmb factor) mulop factor in

  -- Similarly from `E := T | E + T | E - T` we derive that `Expr` is
  -- * a left-nested list of `addop` (i.e. + and -) and `term`
  -- * start with a `term`
  let expr   = hchainl (map EEmb term) addop term in

  -- Going back to the very beginning: we are building a ̀`Language toks mn n`
  -- by recursion. Which means we need to return such a `Language` as a result.
  -- But we have just defined parsers for `Expr`, `Term` and `Factor` so we
  -- can just gather them in the record:
  MkLanguage expr term factor




-- Once we have these parsers, we can write a test:

-- ̀`parse str p` is defined in `TParsec.Running`. It runs the parser `p` on
-- the String `str` and if that succeeds with value `v`, it demands that the
-- give a proof of `Singleton v`. The only such proof is `MkSingleton v`.

-- So if the following `test` typechecks we have the guarantee that running
-- `_expr Arithmetic.language` on `"1+3"` produces the abstract syntax tree
-- `EAdd (EEmb (TEmb (FLit 1))) (TEmb (FLit 3))`. Which it does.

test : parse {mn=Maybe} "1+3" (_expr Arithmetic.language)
test = MkSingleton (EAdd (EEmb (TEmb (FLit 1))) (TEmb (FLit 3)))
