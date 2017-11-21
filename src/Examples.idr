module Examples

import TParsec
import Running

%default total

mutual

 data Expr : Type where
   EEmb : Term -> Expr
   EAdd : Expr -> Term -> Expr
   ESub : Expr -> Term -> Expr

 data Term : Type where
   TEmb : Factor -> Term
   TMul : Term -> Factor -> Term
   TDiv : Term -> Factor -> Term

 data Factor : Type where
   FEmb : Expr -> Factor
   FLit : Nat -> Factor

record Language (toks : Nat -> Type) (mn : Type -> Type) (n : Nat) where
  constructor MkLanguage
  _expr   : Parser toks Char mn Expr n
  _term   : Parser toks Char mn Term n
  _factor : Parser toks Char mn Factor n

language : (Inspect toks Char, Alternative mn, Monad mn) => All (Language toks mn)
language = fix _ $ \ rec =>
  let addop  = alt (cmap EAdd (char '+')) (cmap ESub (char '-')) in
  let mulop  = alt (cmap TMul (char '*')) (cmap TDiv (char '/')) in
  let factor = alt (map FEmb (parens (Induction.map {a=Language _ _} _expr rec)))
                   (map FLit decimalNat) in
  let term   = hchainl (map TEmb factor) mulop factor in
  let expr   = hchainl (map EEmb term) addop term in
  MkLanguage expr term factor


expr : (Inspect toks Char, Alternative mn, Monad mn) =>
       All (Parser toks Char mn Expr)
expr = _expr language

Test : Type
Test = parse {tok=Char} {mn=Maybe} "1+1" expr

test : Test
test = MkSingleton (EAdd (EEmb (TEmb (FLit 1))) (TEmb (FLit 1)))
