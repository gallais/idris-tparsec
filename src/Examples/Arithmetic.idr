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

-- So we define a record `Language` which, given a record of parameters `p`,
-- a monad `mn` and a natural number packs together `Parser`s processing
-- `Toks p` in the monad `mn` to produce respectively values of type `Expr`,
-- `Term`, and `Factor`.

record Language (p : Parameters) (mn : Type -> Type) (n : Nat) where
  constructor MkLanguage
  _expr   : Parser p mn Expr n
  _term   : Parser p mn Term n
  _factor : Parser p mn Factor n

-- We are now ready to build a `Language toks mn n` for all `n` by recursion.
-- We have a few constraints which arise directly from the combinators we are
-- going to use.
-- ̀`Inspect (Toks p) (Tok p)` and `Subset Char (Tok p)` together mean that 
-- `Toks` of `p` can essentially be viewed as a list of `Char`s.
-- In particular, this means that we can make sure that the first character
-- of the input string is a specific `Char` e.g. '+'.

language : (Alternative mn, Monad mn, Instrumented p mn, Inspect (Toks p) (Tok p), Eq (Tok p), Subset Char (Tok p)) => All (Language p mn)
language {p} {mn} =

  -- The value of type `Language` is build as a fixpoint.
  -- We can use the variable `rec` bound here to perform a recursive call.
  fix (Language p mn) $ \rec =>

  -- We start by writing the parsers recognizing basic operations on numbers:
  -- * `alt` is used to take the union of two grammars
  -- * `char c` is used to recognize exactly the character `c`
  -- * `cmap v p` is used to return `v` whenever `p` is a successful parse

  -- From these we can see that:
  let 
  -- `addop` parses either `+` or `-` and returns the right `Expr` constructor
    addop  = cmap EAdd (char '+') `alt` cmap ESub (char '-') 
  -- `mulop` parses either `*` or `/` and returns the right `Term` constructor
    mulop  = cmap TMul (char '*') `alt` cmap TDiv (char '/')

  -- We now need to use some new concepts
  -- * `parens p` parses an opening parenthesis, a value thanks to `p` and then
  --   a closing parenthesis. It returns whatever `p` produced.
  -- * `Nat.map f` applies the function `f` to a recursive call. Here it is
  --   used to project the parser for `Expr` out of `Language`.
  -- * `decimalNat` is a parser for decimal numbers defined in `TParsec.Combinators.Numbers`

  -- `factor` recognizes either an `Expr` in between parentheses or a natural number
    factor = map FEmb (parens (Nat.map {a = Language _ _} _expr rec))
             `alt`
             map FLit decimalNat

  -- We now have all the basic building blocks and can assemble them.

  -- `hchainl base step arg` parses left-nested lists of the form
  -- `((base step arg) step arg) step ...`

  -- Remembering the part of the grammar grammar `T := F | T * F | T / F`
  -- we write the parser for `Term` as:
  -- * a left-nested list of `mulop` (i.e. * and /) and `factor`
  -- * starting with a `factor`.
    term   = hchainl (map TEmb factor) mulop factor

  -- Similarly from `E := T | E + T | E - T` we derive that `Expr` is
  -- * a left-nested list of `addop` (i.e. + and -) and `term`
  -- * start with a `term`
    expr   = hchainl (map EEmb term) addop term 

  -- Going back to the very beginning: we are building a `Language toks mn n`
  -- by recursion. Which means we need to return such a `Language` as a result.
  -- But we have just defined parsers for `Expr`, `Term` and `Factor` so we
  -- can just gather them in the record:
    in
  MkLanguage expr term factor


-- Once we have these parsers, we can write a test:

-- ̀`parse str p` is defined in `TParsec.Running`. It runs the parser `p` on
-- the String `str` and if that succeeds with value `v`, it demands that the
-- user gives a proof of `Singleton v`. The only such proof is `MkSingleton v`.

-- So if the following `test` typechecks we have the guarantee that running
-- `_expr Arithmetic.language` on `"1+3"` produces the abstract syntax tree
-- `EAdd (EEmb (TEmb (FLit 1))) (TEmb (FLit 3))`. Which it does.

test : parse {p = unInstr Char (SizedList Char)} {mn = Maybe} "1+3" (_expr Arithmetic.language)
test = MkSingleton (EAdd (EEmb (TEmb (FLit 1))) (TEmb (FLit 3)))
