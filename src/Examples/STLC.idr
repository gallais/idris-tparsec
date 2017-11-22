module Examples.STLC

import TParsec
import Running
import NEList

%default total

Parser' : Type -> Nat -> Type
Parser' = Parser (SizedList Char) Char Maybe

data TYPE : Type where
  K   : String -> TYPE
  ARR : TYPE -> TYPE -> TYPE

type : All (Parser' TYPE)
type = fix _ $ \ rec => chainr1 (alt (map K (rand (char '\'') alphas)) (parens rec))
                                (cmap ARR (withSpaces (string "->")))

Test : Type
Test = parse {tok = Char} {mn = Maybe} "'a -> ('b -> 'c) -> 'd" type

test : Test
test = MkSingleton (ARR (K "a") (ARR (ARR (K "b") (K "c")) (K "d")))

mutual

  data Val : Type where
    Lam : String -> Val -> Val
    Emb : Neu -> Val

  data Neu : Type where
    Var : String -> Neu
    Cut : Val -> TYPE -> Neu
    App : Neu -> Val -> Neu

record Language (n : Nat) where
  constructor MkLanguage
  val : Parser' Val n
  neu : Parser' Neu n

var : All (Parser' String)
var = alphas

cut : All (Box (Parser' Val) :-> Parser' (Pair Val TYPE))
cut rec = parens (adjust rec (rand (withSpaces (char ':')) type)) where

  adjust : All (Box (Parser' s) :-> Parser' t :-> Box (Parser' (Pair s t)))
  adjust {s} {t} p q = map2 {a=Parser' s} {b=Parser' t} (\ p, q => Combinators.and p q) p q

neu : All (Box (Parser' Val) :-> Parser' Neu)
neu rec = hchainl (alt (map Var var) (map (uncurry Cut) (cut rec))) (cmap App spaces) rec

lam : All (Box (Parser' Val) :-> Parser' (Pair String Val))
lam rec = rand (char '\\') (and (withSpaces var) (rand (andm (char '.') spaces) rec))

val : All (Box (Parser' Val) :-> Parser' Val)
val rec = alt (map (uncurry Lam) (lam rec)) (map Emb (neu rec))

language : All Language
language = fix Language $ \ rec =>
  let ihv = Induction.map {a=Language} val rec in
  MkLanguage (val ihv) (neu ihv)

Test2 : Type
Test2 = parse {tok=Char} {mn=Maybe} "\\ x . (\\ y . y : 'a -> 'a) x" (val language)

test2 : Test2
test2 = MkSingleton (Lam "x" (Emb (App (Cut (Lam "y" (Emb (Var "y"))) (ARR (K "a") (K "a")))
                                       (Emb (Var "x")))))
