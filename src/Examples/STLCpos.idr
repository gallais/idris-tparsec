module Examples.STLCpos

import Control.Monad.State
import Data.NEList
import TParsec
import TParsec.Running

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
    lt = alt (map K (rand (char '\'') (box alphas))) (parens rec)
    arr = cmap ARR (withSpaces (string "->"))
    in
  chainr1 lt (box arr)

{-
Test : Type
Test = (parseResult "'a -> ('b -> 'c) -> 'd" type = Value $ Just $ ARR (K "a") (ARR (ARR (K "b") (K "c")) (K "d")))

test : Test
test = Refl
-}
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

ident : All (Parser' String)
ident = alphas

var : All (Parser' Neu)
var = map Var ident

cut : All (Box (Parser' Val) :-> Parser' Neu)
cut rec = map (\(v,p,t) => Cut p v t) $ 
          parens (andbox (Nat.map {a=Parser' _} commit rec)
                         (and (withSpaces (lmand getPosition (char ':'))) 
                              type))
  where
    andbox : All (Box (Parser' s) :-> Parser' t :-> Box (Parser' (s, t)))
    andbox p q =
      Nat.map2 {a=Parser' _} {b=Parser' _} (\p, q => Combinators.and p q) p q

app : All (Box (Parser' Val) :-> Parser' Val)
app rec = alt (map (uncurry Emb) $ mand getPosition var) (parens rec)

neu : All (Box (Parser' Val) :-> Box (Parser' Neu) :-> Parser' Neu)
neu recv recn = 
  hchainl 
    (alts [ var
          , cut recv
          , parens recn
          ]) 
    (map STLCpos.App $ randm space getPosition) 
    (app recv)
      
lam : All (Box (Parser' Val) :-> Parser' Val)
lam rec = map (\((p,s),v) => Lam p s v) $ 
          rand (char '\\') 
               (and (mand getPosition 
                          (withSpaces ident)) 
                    (rand (andopt (char '.') spaces) 
                          (Nat.map {a=Parser' _} commit rec)))

emb : All (Box (Parser' Val) :-> Box (Parser' Neu) :-> Parser' Val)
emb recv recn = map (uncurry Emb) $ mand getPosition (neu recv recn)
        
val : All (Box (Parser' Val) :-> Box (Parser' Neu) :-> Parser' Val)
val recv recn = 
  alts [ lam recv 
       , emb recv recn
       , parens recv
       ]

stlc : All STLC
stlc = fix _ $ \rec =>
  let 
    ihv = Nat.map {a=STLC} val rec 
    ihn = Nat.map {a=STLC} neu rec 
   in
  MkSTLC (val ihv ihn) (neu ihv ihn)

{-
Test2 : Type
Test2 = parseResult "\\x.(\\y.y:'a->'a) x" (val stlc) = Value $ Just $ 
                                                        Lam (MkPosition 0 1) "x" $
                                                          Emb (MkPosition 0 3) $
                                                            App (MkPosition 0 17)
                                                                (Cut (MkPosition 0 8)
                                                                     (Lam (MkPosition 0 5) "y" $
                                                                       Emb (MkPosition 0 7) (Var "y"))
                                                                     (ARR (K "a") (K "a")))
                                                                (Emb (MkPosition 0 17) (Var "x"))

test2 : Test2
test2 = Refl

Test3 : Type
Test3 = parseResult "\\x.1:'a->'a" (val stlc) = HardFail $ ParseError $ MkPosition 0 3

test3 : Test3
test3 = Refl

Test4 : Type
Test4 = parseResult "\\g.\\f.\\a.g a (f a)" (val stlc) = Value $ Just $
                                                         Lam (MkPosition 0 1) "g" $
                                                           Lam (MkPosition 0 4) "f" $
                                                             Lam (MkPosition 0 7) "a" $
                                                               Emb (MkPosition 0 9) $ 
                                                                 App (MkPosition 0 13)
                                                                     (App (MkPosition 0 11) 
                                                                          (Var "g") 
                                                                          (Emb (MkPosition 0 11) (Var "a")))
                                                                     (Emb (MkPosition 0 14) $ App (MkPosition 0 16) 
                                                                                                  (Var "f") 
                                                                                                  (Emb (MkPosition 0 16) (Var "a")))

test4 : Test4
test4 = Refl

Test5 : Type
Test5 = parseResult "\\g.\\f.\\a.(g a) (f a)" (val stlc) = Value $ Just $ 
                                                           Lam (MkPosition 0 1) "g" $
                                                             Lam (MkPosition 0 4) "f" $
                                                               Lam (MkPosition 0 7) "a" $
                                                                 Emb (MkPosition 0 9) $ 
                                                                   App (MkPosition 0 15)
                                                                       (App (MkPosition 0 12)
                                                                            (Var "g") 
                                                                            (Emb (MkPosition 0 12) (Var "a")))
                                                                       (Emb (MkPosition 0 16) $ App (MkPosition 0 18) 
                                                                                                    (Var "f") 
                                                                                                    (Emb (MkPosition 0 18) (Var "a")))

test5 : Test5
test5 = Refl
-}
