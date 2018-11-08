module Examples.STLCpos

import Control.Monad.State
import Data.NEList
import TParsec
import TParsec.Running

%default total

data TYPE : Type where
  K   : String -> TYPE
  ARR : TYPE -> TYPE -> TYPE

data Error : Type where
  ParseError  : Position -> Error
-- OutOfScope  : Position -> String -> Error
-- ExpectedGot : Position -> TYPE -> TYPE -> Error
-- NotAnArrow  : Position -> TYPE -> Error

Parser' : Type -> Nat -> Type
Parser' = Parser (TParsecM Error Void) chars

Subset (Position, List Void) Error where
  into = ParseError . fst

type : All (Parser' TYPE)
type =
  fix _ $ \rec =>
  let
    lt = alt (map K (rand (char '\'') alphas)) (parens rec)
    arr = cmap ARR (withSpaces (string "->"))
    in
  chainr1 lt arr

Test : Type
Test = parseResult "'a -> ('b -> 'c) -> 'd" type = Value (ARR (K "a") (ARR (ARR (K "b") (K "c")) (K "d")))

test : Test
test = Refl

mutual
  data Val : Type where
    Lam : Position -> String -> Val -> Val
    Emb : Position -> Neu -> Val

  data Neu : Type where
    Var : String -> Neu
    Cut : Position -> Val -> TYPE -> Neu
    App : Position -> Neu -> Val -> Neu

record STLC (n : Nat) where
  constructor MkSTLC
  val : Parser' Val n
  neu : Parser' Neu n

name : All (Parser' String)
name = alphas

var : All (Parser' Neu)
var = map Var name

cut : All (Box (Parser' Val) :-> Parser' Neu)
cut rec = map (\(v,p,t) => Cut p v t) $ 
          parens (andbox (Nat.map {a=Parser' _} commit rec)
                         (and (withSpaces (lmand getPosition (char ':'))) 
                              type))
  where
    andbox : All (Box (Parser' s) :-> Parser' t :-> Box (Parser' (s, t)))
    andbox p q =
      Nat.map2 {a=Parser' _} {b=Parser' _} (\p, q => Combinators.and p q) p q


app : All (Parser' (Neu -> Val -> Neu))
app = map App $ randm space getPosition

neu : All (Box (Parser' Val) :-> Parser' Neu)
neu rec = hchainl (var `alt` (cut rec)) app rec 
      
lam : All (Box (Parser' Val) :-> Parser' Val)
lam rec = map (\((p,s),v) => Lam p s v) $ 
          rand (char '\\') 
               (and (mand getPosition 
                          (withSpaces name)) 
                    (rand (andopt (char '.') spaces) 
                          (Nat.map {a=Parser' _} commit rec)))

emb : All (Box (Parser' Val) :-> Parser' Val)
emb rec = map (uncurry Emb) $ mand getPosition (neu rec)
        
val : All (Box (Parser' Val) :-> Parser' Val)
val rec = (lam rec) `alt` (emb rec)

stlc : All STLC
stlc = fix _ $ \rec =>
  let ihv = Nat.map {a=STLC} val rec in
  MkSTLC (val ihv) (neu ihv)

Test2 : Type
Test2 = parseResult "\\ x . (\\ y . y : 'a -> 'a) x" (val stlc) = Value (Lam (MkPosition 0 1) "x" 
                                                                         (Emb (MkPosition 0 6) 
                                                                          (App (MkPosition 0 27) 
                                                                           (Cut (MkPosition 0 15) 
                                                                            (Lam (MkPosition 0 8) "y" 
                                                                             (Emb (MkPosition 0 13) (Var "y"))) 
                                                                            (ARR (K "a") (K "a"))) 
                                                                           (Emb (MkPosition 0 27) (Var "x"))))) 

test2 : Test2
test2 = Refl

Test3 : Type
Test3 = parseResult "\\ x . 1 : 'a -> 'a" (val stlc) = HardFail (ParseError (MkPosition 0 7))

test3 : Test3
test3 = Refl
