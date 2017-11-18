module Combinators

import Indexed
import Induction as Box
import Inspect
import Success

%default total
%access public export

record Parser (toks : Nat -> Type) (tok : Type)
              (mn : Type -> Type) (a : Type) (n : Nat) where
  constructor MkParser
  runParser : {m : Nat} -> LTE m n -> toks m -> mn (Success toks tok a m)

lteLower : LTE m n -> Parser toks tok mn a n -> Parser toks tok mn a m
lteLower mlen p = MkParser (\ plem => runParser p (lteTransitive plem mlen))

ltLower : LT m n -> Parser toks tok mn a n -> Parser toks tok mn a m
ltLower mltn = lteLower (lteSuccLeft mltn)

implicit box : All (Parser toks tok mn a :-> Box (Parser toks tok mn a))
box = lteClose lteLower

anyTok : (Inspect toks tok, Alternative mn) =>
         All (Parser toks tok mn tok)
anyTok = MkParser (\ mlen, ts => choiceMap pure (getTok ts))

guardM : (Alternative mn, Monad mn) =>
         (a -> Maybe b) -> All (Parser toks tok mn a :-> Parser toks tok mn b)
guardM f p = MkParser (\ mlen, ts => runParser p mlen ts >>= \ s =>
                       choiceMap pure (Success.guardM f s))

map : Functor mn =>
      (a -> b) -> All (Parser toks tok mn a :-> Parser toks tok mn b)
map f p = MkParser (\ le, ts => Functor.map (Success.map f) (runParser p le ts))

cmap : Functor mn => b -> All (Parser toks tok mn a :-> Parser toks tok mn b)
cmap b = map (\ _ => b)

fail : Alternative mn => All (Parser toks tok mn a)
fail = MkParser (\ _, _ => empty)

alt : Alternative mn =>
      All (Parser toks tok mn a :-> Parser toks tok mn a :->
           Parser toks tok mn a)
alt p q = MkParser (\ mlen, ts => runParser p mlen ts <|> runParser q mlen ts)

alts : Alternative mn =>
       All (List :. Parser toks tok mn a :-> Parser toks tok mn a)
alts = foldr (\ p, q => alt p q) fail
