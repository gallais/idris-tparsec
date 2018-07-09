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
  OutOfScope  : Position -> String -> Error
  ExpectedGot : Position -> TYPE -> TYPE -> Error
  NotAnArrow  : Position -> TYPE -> Error

Pars : Parameters
Pars = posAnn Char (\n => Vect n Char) Void

PosM : Type -> Type
PosM = StateT Position (Either Error)

-- named because there stdlib already gives us (Monad f, Alternative f) => Alternative (StateT st f) which we can't use here
[altpos] Alternative PosM where
  empty = ST $ Left . ParseError
  (ST a) <|> (ST b) = ST $ \pos => case a pos of 
                                     Left _ => b pos
                                     Right x => Right x

-- named because of lambda in the type                                     
[isvect] Inspect (\n => Vect n Char) Char where
  inspect []        = Nothing
  inspect (x :: xs) = Just (x, xs)

[invect] Instrumented Pars PosM where
  withAnnotation Void _ impossible
  recordToken c = ST $ \pos => Right ((), next c pos)
  getPosition = ST $ \pos => Right (pos, pos)
  getAnnotation = ST $ \pos => Right (Nothing, pos)

Parser' : Type -> Nat -> Type
Parser' = Parser Pars PosM

parse' : String -> All (Parser' a) -> Either Error a
parse' str p = let st = runParser p lteRefl $ fromList $ tokenize str in 
               case runStateT st start of 
                Left err => Left err
                Right (s, _) => Right $ Value s

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
Test = parse' "'a -> ('b -> 'c) -> 'd" type = Right (ARR (K "a") (ARR (ARR (K "b") (K "c")) (K "d")))

test : Test
test = Refl

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
  val : Parser' (Position, Val) n
  neu : Parser' (Position, Neu) n

using implementation altpos 
  using implementation isvect 
    using implementation invect 
      var : All (Parser' String)
      var = alphas

      cut : All (Box (Parser' Val) :-> Parser' (Val, Position, TYPE))
      cut rec = parens (adjust rec (and (withSpaces (lmand getPosition (char ':'))) type)) where
        adjust : All (Box (Parser' s) :-> Parser' t :-> Box (Parser' (s, t)))
        adjust p q =
          Nat.map2 {a=Parser' _} {b=Parser' _} (\p, q => Combinators.and p q) p q

      neu : All (Box (Parser' Val) :-> Parser' (Position, Neu))
      neu rec = 
        hchainl ((map (\s => MkPair {A=Position} {B=Neu} start (Var s)) var) `alt` (map (\(v,p,t) => (p, Cut v t)) (cut rec)))  
                (Combinators.map (\p, (_, n), v => (p, App n v)) (randm space getPosition))
                rec 
      
      lam : All (Box (Parser' Val) :-> Parser' ((Position, String), Val))
      lam rec = rand (char '\\') (and (mand getPosition (withSpaces var)) (rand (andopt (char '.') spaces) rec))
        
      val : All (Box (Parser' Val) :-> Parser' (Position, Val))
      val rec = alt (map (\((p,s),v) => (p, Lam s v)) (lam rec)) (mand getPosition (map (\(_, n) => Emb n) (neu rec)))

language : All Language
language = fix _ $ \rec =>
  let ihv = Nat.map {a=Language} (map snd . val) rec in
  MkLanguage (val ihv) (neu ihv)
  
Test2 : Type
Test2 = parse' "\\ x . (\\ y . y : 'a -> 'a) x" (val language) = Right (MkPosition 0 1, Lam "x" (Emb (App (Cut (Lam "y" (Emb (Var "y"))) (ARR (K "a") (K "a"))) (Emb (Var "x")))))

test2 : Test2
test2 = Refl
