module Induction.Nat

import Data.Nat
import Relation.Indexed

%default total

public export
record Box (a : Nat -> Type) (n : Nat) where
  constructor MkBox
  call : {m : Nat} -> (0 prf : LT m n) -> a m

public export
ltClose : ({0 m, n : Nat} -> (0 prf : LT m n) -> a n -> a m) -> All (a :-> Box a)
ltClose down a = MkBox $ \lt => down lt a

public export
lteClose : ({0 m, n : Nat} -> (0 prf : LTE m n) -> a n -> a m) -> All (a :-> Box a)
lteClose down = ltClose $ \lt => down (lteSuccLeft lt)

public export
map : All (a :-> b) -> All (Box a :-> Box b)
map f a = MkBox $ \lt => f (call a lt)

public export
map2 : All (a :-> b :-> c) -> All (Box a :-> Box b :-> Box c)
map2 f a b = MkBox $ \lt => f (call a lt) (call b lt)

public export
app : All (Box (a :-> b) :-> Box a :-> Box b)
app f a = MkBox $ \lt => (call f lt) (call a lt)

public export
extract : All (Box a) -> All a
extract a = call a lteRefl

public export
duplicate : All (Box a :-> Box (Box a))
duplicate a = MkBox $ \mltn => MkBox $ \pltm =>
              call a (lteTransitive pltm (lteSuccLeft mltn))

public export
lteLower : (0 prf : LTE m n) -> Box a n -> Box a m
lteLower mlen b = MkBox $ \pltm => call b (lteTransitive pltm mlen)

public export
ltLower : (0 prf : LT m n) -> Box a n -> Box a m
ltLower prf = lteLower (lteSuccLeft prf)

public export
fixBox : All (Box a :-> a) -> All (Box a)
fixBox alg = go _
  where
  go : (n : Nat) -> Box a n
  go  Z    = MkBox (\ pr => void (absurd pr))
  go (S n) = MkBox $ \mltSn => alg (lteLower (fromLteSucc mltSn) (go n))

public export
fix : (0 t : Nat -> Type) -> All (Box t :-> t) -> All t
fix _ = extract . fixBox

public export
loeb : All (Box (Box a :-> a) :-> Box a)
loeb = fix (Box (Box a :-> a) :-> Box a) (\ rec, f =>
         MkBox (\ lt => call f lt (call rec lt (call (duplicate f) lt))))
