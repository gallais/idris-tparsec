module Examples.NList

import Data.DList
import TParsec
import TParsec.Running

%default total

NList : Type -> Nat -> Type
NList a  Z    = a
NList a (S n) = List (NList a n)

Parser' : Type -> Nat -> Type
Parser' = Parser TParsecU chars

NList' : All (Parser' a) -> (n : Nat) -> All (Parser' (NList a n))
NList' a  Z    = a
NList' a (S n) = parens $ box $ map DList.toList (chainl1 (map wrap (NList' a n)) (box $ cmap (++) (char ',')))

---- tests

nnats : (n : Nat) -> All (Parser' (NList Nat n))
nnats = NList' decimalNat

test : parseType "((1,2,3),(4,5,6))" (nnats 2)
test = MkSingleton [[1, 2, 3], [4, 5, 6]]

test2 : parseType "((1,2,3),(4,5,6),(7,8,9,10))" (nnats 2)
test2 = MkSingleton [[1, 2, 3], [4, 5, 6], [7, 8, 9, 10]]

test3 : parseType "((1),(2))" (nnats 2)
test3 = MkSingleton [[1], [2]]

test4 : parseType "((1,2))" (nnats 2)
test4 = MkSingleton [[1, 2]]

test5 : parseType "(((1,2),(3,4)),((5,6),(7,8)))" (nnats 3)
test5 = MkSingleton [[[1, 2], [3, 4]], [[5, 6], [7, 8]]]
