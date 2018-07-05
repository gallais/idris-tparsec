-- Difference lists

module Data.DList

%default total
%access public export

DList : Type -> Type
DList a = List a -> List a

lift : (List a -> List a) -> (DList a -> DList a)
lift f xs = f . xs

nil : DList a
nil = id

cons : a -> DList a -> DList a
cons x = lift (x ::)

wrap : a -> DList a
wrap x = cons x nil

(++) : DList a -> DList a -> DList a
(++) xs ys = xs . ys

toList : DList a -> List a
toList xs = xs []