module Induction.Nat

import Relation.Indexed

%access public export
%default total

record Box (a : Nat -> Type) (n : Nat) where
  constructor MkBox
  call : {m : Nat} -> LT m n -> a m

ltClose : ({m, n : Nat} -> LT m n -> a n -> a m) -> All (a :-> Box a)
ltClose down a = MkBox (\ lt => down lt a)

lteClose : ({m, n : Nat} -> LTE m n -> a n -> a m) -> All (a :-> Box a)
lteClose down = ltClose (\ lt => down (lteSuccLeft lt))

pure : All a -> All (Box a)
pure a = MkBox (\ _ => a)

map : (f : All (a :-> b)) -> All (Box a :-> Box b)
map f a = MkBox (\ lt => f (call a lt))

map2 : (f : All (a :-> b :-> c)) -> All (Box a :-> Box b :-> Box c)
map2 f a b = MkBox (\ lt => f (call a lt) (call b lt))

app : All (Box (a :-> b) :-> Box a :-> Box b)
app f a = MkBox (\ lt => (call f lt) (call a lt))

extract : All (Box a) -> All a
extract a = call a lteRefl

duplicate : All (Box a :-> Box (Box a))
duplicate a = MkBox (\ mltn => MkBox (\ pltm =>
              call a (lteTransitive pltm (lteSuccLeft mltn))))

lteLower : LTE m n -> Box a n -> Box a m
lteLower mlen b = MkBox (\ pltm => call b (lteTransitive pltm mlen))

ltLower : LT m n -> Box a n -> Box a m
ltLower p = lteLower (lteSuccLeft p)

fixBox : All (Box a :-> a) -> All (Box a)
fixBox {a} alg = go _ where

  go : (n : Nat) -> Box a n
  go Z     = MkBox absurd
  go (S n) = MkBox (\ mltSn => alg (lteLower (fromLteSucc mltSn) (go n)))

fix : (a : Nat -> Type) -> All (Box a :-> a) -> All a
fix a alg = extract (fixBox alg)

loeb : All (Box (Box a :-> a) :-> Box a)
loeb {a} = fix (Box (Box a :-> a) :-> Box a) (\ rec, f =>
            MkBox (\ lt => call f lt (call rec lt (call (duplicate f) lt))))
