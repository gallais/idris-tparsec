module TParsec.Success

import Relation.Indexed
import Data.Inspect

%default total
%access public export

-- A successful partial parse of an A is a value A together leftovers
-- which are proven to be smaller than the input

record Success (toks : Nat -> Type) (a : Type) (n : Nat) where
  constructor MkSuccess
  Value     : a
  {Size      : Nat}
  Small     : LT Size n
  Leftovers : toks Size

map : (f : a -> b) -> All (Success toks a :-> Success toks b)
map f (MkSuccess v lt ts) = MkSuccess (f v) lt ts

guardM : (a -> Maybe b) -> All (Success toks a :-> Maybe :. Success toks b)
guardM p (MkSuccess v lt ts) = Functor.map (\ v => MkSuccess v lt ts) (p v)

lteLift : LTE m n -> Success toks a m -> Success toks a n
lteLift mlen (MkSuccess v sltm ts) = MkSuccess v (lteTransitive sltm mlen) ts

ltLift : LT m n -> Success toks a m -> Success toks a n
ltLift p = lteLift (lteSuccLeft p)

and : (p : Success toks a n) -> Success toks b (Size p) ->
      Success toks (a, b) n
and p q = ltLift (Small p) (map (MkPair (Value p)) q)

fromView : All (View toks tok :-> Success toks tok)
fromView = go _ where

  go : (n : Nat) -> View toks tok n -> Success toks tok n
  go Z     v       = absurd v
  go (S n) (v, vs) = MkSuccess v lteRefl vs

getTok : Inspect toks tok => All (toks :-> Maybe :. Success toks tok)
getTok {toks} {tok} ts = Functor.map fromView (inspect {As=toks} {A=tok} ts)
