module Inspect

import Indexed
import SizedDict

%default total
%access public export

View : (as : Nat -> Type) -> (a : Type) -> (n : Nat) -> Type
View as a Z     = Void
View as a (S n) = Pair a (as n)

interface Inspect (As : Nat -> Type) (A : Type) where
  inspect : All (As :-> Maybe :. View As A)

record SizedType (a : Type) (n : Nat) where
  constructor MkSizedType
  Dict  : SizedDict a
  Value : a
  Sized : sizeFromDict Dict Value = n

SizedList : Type -> Nat -> Type
SizedList a n = SizedType (List a) n

Inspect (SizedType (List a)) a where
  inspect (MkSizedType MkSizedDict v s) = go _ v s where

    go : (n : Nat) -> (xs : List a) -> List.length xs = n ->
         Maybe (View (SizedType (List a)) a n)
    go Z      _         _ = Nothing
    go (S n) (x :: xs) eq = let eq' = succInjective _ _ eq
                            in Just (x, MkSizedType MkSizedDict xs eq')
    go (S n) [] Refl impossible
