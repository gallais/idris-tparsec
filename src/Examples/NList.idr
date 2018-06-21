module Examples.NList

import TParsec
import TParsec.Running

%default total

-- Difference lists

namespace DList

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

----

NList : Type -> Nat -> Type
NList a  Z    = a
NList a (S n) = List (NList a n)

Parser' : Type -> Nat -> Type
Parser' = Parser (SizedList Char) Char Maybe

NList' : All (Parser' a) -> (n : Nat) -> All (Parser' (NList a n))
NList' a  Z    = a
NList' a (S n) = parens $ map DList.toList (chainl1 (map wrap (NList' a n)) (cmap (++) (char ',')))

---- tests

nnats : (n : Nat) -> All (Parser' (NList Nat n))
nnats = NList' decimalNat

test : parse "((1,2,3),(4,5,6))" (nnats 2)
test = MkSingleton [[1, 2, 3], [4, 5, 6]]

test2 : parse "((1,2,3),(4,5,6),(7,8,9,10))" (nnats 2)
test2 = MkSingleton [[1, 2, 3], [4, 5, 6], [7, 8, 9, 10]]

test3 : parse "((1),(2))" (nnats 2)
test3 = MkSingleton [[1], [2]]

test4 : parse "((1,2))" (nnats 2)
test4 = MkSingleton [[1, 2]]

test5 : parse "(((1,2),(3,4)),((5,6),(7,8)))" (nnats 3)
test5 = MkSingleton [[[1, 2], [3, 4]], [[5, 6], [7, 8]]]
