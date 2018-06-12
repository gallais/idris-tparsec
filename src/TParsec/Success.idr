module TParsec.Success

import TParsec.Indexed
import TParsec.Inspect

%default total
%access public export

record Success (toks : Nat -> Type) (tok : Type) (a : Type) (n : Nat) where
  constructor MkSuccess
  Value     : a
  Size      : Nat
  Small     : LT Size n
  Leftovers : toks Size

map : (f : a -> b) -> All (Success toks tok a :-> Success toks tok b)
map f (MkSuccess v s lt ts) = MkSuccess (f v) s lt ts

guardM : (a -> Maybe b) -> All (Success toks tok a :-> Maybe :. Success toks tok b)
guardM p (MkSuccess v s lt ts) = Functor.map (\ v => MkSuccess v s lt ts) (p v)

lteLift : LTE m n -> Success toks tok a m -> Success toks tok a n
lteLift mlen (MkSuccess v s sltm ts) = MkSuccess v s (lteTransitive sltm mlen) ts

ltLift : LT m n -> Success toks tok a m -> Success toks tok a n
ltLift p = lteLift (lteSuccLeft p)

and : (p : Success toks tok a n) -> Success toks tok b (Size p) ->
      Success toks tok (Pair a b) n
and p q = ltLift (Small p) (map (MkPair (Value p)) q)

fromView : All (View toks tok :-> Success toks tok tok)
fromView = go _ where

  go : (n : Nat) -> View toks tok n -> Success toks tok tok n
  go Z     v       = absurd v
  go (S n) (v, vs) = MkSuccess v n lteRefl vs

getTok : Inspect toks tok => All (toks :-> Maybe :. Success toks tok tok)
getTok {toks} {tok} ts = Functor.map fromView (inspect {As=toks} {A=tok} ts)
