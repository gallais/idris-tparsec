module TParsec.Success

import Data.Nat
import Data.Maybe
import Relation.Indexed
import Data.Inspect
import Data.Vect

%default total

-- A successful partial parse of an A is a value A together leftovers
-- which are proven to be smaller than the input

public export
record Success (toks : Nat -> Type) (a : Type) (n : Nat) where
  constructor MkSuccess
  Value     : a
  {Size     : Nat}
  0 Small   : LT Size n
  Leftovers : toks Size

public export
complete : Success toks a n -> Maybe a
complete s = toMaybe (Size s == Z) (Value s)

public export
map : (a -> b) -> All (Success toks a :-> Success toks b)
map f (MkSuccess v lt ts) = MkSuccess (f v) lt ts

public export
guardM : (a -> Maybe b) -> All (Success toks a :-> Maybe :. Success toks b)
guardM p (MkSuccess v lt ts) = map (\v => MkSuccess v lt ts) (p v)

public export
lteLift : (0 prf : LTE m n) -> Success toks a m -> Success toks a n
lteLift mlen (MkSuccess v sltm ts) = MkSuccess v (lteTransitive sltm mlen) ts

public export
ltLift : (0 prf : LT m n) -> Success toks a m -> Success toks a n
ltLift prf = lteLift (lteSuccLeft prf)

public export
and : (p : Success toks a n) -> Success toks b (Size p) ->
      Success toks (a, b) n
and p q = ltLift (Small p) (map (MkPair (Value p)) q)

public export
fromView : All (View toks tok :-> Success toks tok)
fromView = go _
  where
  go : (n : Nat) -> View toks tok n -> Success toks tok n
  go  Z     v      = absurd v
  go (S n) (v, vs) = MkSuccess v lteRefl vs

public export
getTok : Inspect toks tok => All (toks :-> Maybe :. Success toks tok)
getTok ts = map fromView (inspect {as=toks} {a=tok} ts)
