module Examples.STLCins

import Control.Monad.State
import Data.Vect
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

Pars : Parameters
Pars = posAnn Char (\n => Vect n Char) Void

data Result : Type -> Type where
  HardFail : Error -> Result a
  SoftFail : Error -> Result a
  Value : a -> Result a

Functor Result where
  map _ (HardFail e) = HardFail e
  map _ (SoftFail e) = SoftFail e
  map f (Value a)    = Value (f a)

Applicative Result where
  pure = Value
  (HardFail e) <*> _ = HardFail e
  (SoftFail e) <*> _ = SoftFail e
  _ <*> (HardFail e) = HardFail e
  _ <*> (SoftFail e) = SoftFail e
  (Value f) <*> (Value a) = Value (f a)

Monad Result where
  (HardFail e) >>= _ = HardFail e
  (SoftFail e) >>= _ = SoftFail e
  (Value a)    >>= f = f a

PosM : Type -> Type
PosM = StateT Position Result  

commitPos : PosM a -> PosM a
commitPos (ST ma) = ST $ \pos => case ma pos of 
  SoftFail e => HardFail e
  r => r

-- named because there stdlib already gives us (Monad f, Alternative f) => Alternative (StateT st f) which we can't use here
[altpos] Alternative PosM where
  empty = ST $ SoftFail . ParseError
  (ST a) <|> (ST b) = ST $ \pos => case a pos of 
                                     SoftFail _ => b pos
                                     r => r


-- named because of lambda in the type                                     
[isvect] Inspect (\n => Vect n Char) Char where
  inspect []        = Nothing
  inspect (x :: xs) = Just (x, xs)

[invect] Instrumented Pars PosM where
  withAnnotation Void _ impossible
  recordToken c = ST $ \pos => Value ((), next c pos)
  getPosition   = ST $ \pos => Value (pos, pos)
  getAnnotation = ST $ \pos => Value (Nothing, pos)

Parser' : Type -> Nat -> Type
Parser' = Parser Pars PosM

commit : All (Parser' a :-> Parser' a)
commit p = MkParser $ \mlen, ts => commitPos $ runParser p mlen ts

parse' : String -> All (Parser' a) -> Result a
parse' str p = let st = runParser p lteRefl $ fromList $ tokenize str in 
               map (Success.Value . fst) $ runStateT st start

using implementation altpos 
  using implementation isvect 
    using implementation invect 
      type : All (Parser' TYPE)
      type =
        fix _ $ \rec =>
        let
          lt = alt (map K (rand (char '\'') alphas)) (parens rec)
          arr = cmap ARR (withSpaces (string "->"))
          in
        chainr1 lt arr

Test : Type
Test = parse' "'a -> ('b -> 'c) -> 'd" type = Value (ARR (K "a") (ARR (ARR (K "b") (K "c")) (K "d")))

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

using implementation altpos 
  using implementation isvect 
    using implementation invect 
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
      app = map App $ randm space (getPosition {p=Pars})

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
      emb rec = map (uncurry Emb) $ mand (getPosition {p=Pars}) (neu rec)
        
      val : All (Box (Parser' Val) :-> Parser' Val)
      val rec = (lam rec) `alt` (emb rec)

stlc : All STLC
stlc = fix _ $ \rec =>
  let ihv = Nat.map {a=STLC} val rec in
  MkSTLC (val ihv) (neu ihv)

Test2 : Type
Test2 = parse' "\\ x . (\\ y . y : 'a -> 'a) x" (val stlc) = Value (Lam (MkPosition 0 1) "x" 
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
Test3 = parse' "\\ x . 1 : 'a -> 'a" (val stlc) = HardFail (ParseError (MkPosition 0 7))

test3 : Test3
test3 = Refl