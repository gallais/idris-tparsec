module Examples.Ambig

import Data.List
import Data.Vect
import Data.Nat
import Control.Monad.State
import Data.NEList
import TParsec
import TParsec.Running

%default total

record PosOr (a : Type) where
  constructor MkPO
  runPO : StateT Position (Either Position) a

Parser' : Type -> Nat -> Type
Parser' = Parser PosOr
                (MkParameters Char
                              (\n => Vect n Char)
                              (\c => MkPO $ ST $ \pos => Right ((), update c pos)))

Functor PosOr where
  map f (MkPO a) = MkPO $ map f a

Applicative PosOr where
  pure a = MkPO $ pure a
  (MkPO f) <*> (MkPO a) = MkPO $ f <*> a

-- choose the one parsed the furthest
heuristic : Position -> Position -> Position
heuristic p1@(MkPosition r1 c1) p2@(MkPosition r2 c2) =
  case compare r2 r1 of
    LT => p1
    GT => p2
    EQ => if c1>c2 then p1 else p2

Alternative PosOr where
  empty = MkPO $ ST $ Left
  (MkPO (ST a)) <|> (MkPO (ST b)) = MkPO $ ST $ \pos =>
    case a pos of
      Right x => Right x
      Left e1 => case b pos of
        Right x => Right x
        Left e2 => Left $ heuristic e1 e2

Monad PosOr where
  (MkPO a) >>= f = MkPO $ a >>= (runPO . f)

parse' : String -> All (Parser' a) -> Either Position a
parse' str p = let st = runParser p lteRefl $ sizedInput {toks= \n=>Vect n Char} $ tokenize {tok=Char} str in
               map (Success.Value . fst) $ runStateT (runPO st) start

Amb : All (Parser' Unit)
Amb = cmap () $ string "abracadabra" `alt` string "abraham"

test : parse' "abracadazra" Amb = Left (MkPosition 0 9)
test = Refl