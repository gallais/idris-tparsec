module Data.Inspect

import Relation.Indexed
import Data.Vect

%default total

public export
View : (as : Nat -> Type) -> (a : Type) -> (n : Nat) -> Type
View as a  Z    = Void
View as a (S n) = (a, as n)

public export
interface Inspect (0 as : Nat -> Type) (0 a : Type) where
  inspect : All (as :-> Maybe :. View as a)

public export
Inspect (\n => Vect n a) a where
  inspect [] = Nothing
  inspect (x::xs) = Just (x, xs)
