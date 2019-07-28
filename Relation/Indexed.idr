module Relation.Indexed

infixr 1 :->
public export
(:->) : (a, b : i -> Type) -> (i -> Type)
(:->) a b i = a i -> b i

infixr 2 :+
public export
(:+) : (a, b : i -> Type) -> (i -> Type)
(:+) a b i = Either (a i) (b i)

infixr 3 :*
public export
(:*) : (a, b : i -> Type) -> (i -> Type)
(:*) a b i = (a i, b i)

infixr 4 :.
public export
(:.) : (t : Type -> Type) -> (a : i -> Type) -> (i -> Type)
(:.) t a i = t (a i)

public export
Cst : Type -> (i -> Type)
Cst t i = t

public export
All : (a : i -> Type) -> Type
All {i} a = {j : i} -> a j
