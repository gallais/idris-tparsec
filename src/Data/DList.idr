-- Difference lists

module Data.DList

%default total

public export
record DList (a : Type) where
  constructor MkDList
  runDList : List a -> List a

public export
toList : DList a -> List a
toList xs = runDList xs []

public export
fromList : List a -> DList a 
fromList = MkDList . (++)

public export
lift : (List a -> List a) -> (DList a -> DList a)
lift f (MkDList fx) = MkDList $ f . fx

public export
nil : DList a
nil = MkDList id

public export
cons : a -> DList a -> DList a
cons x = lift (x ::)

public export
snoc : DList a -> a -> DList a
snoc (MkDList fx) x = MkDList $ fx . (x ::)

public export
wrap : a -> DList a
wrap x = cons x nil

public export
(++) : DList a -> DList a -> DList a
(++) (MkDList fx) = lift fx

public export
replicate : Nat -> a -> DList a
replicate n x = MkDList $ \xs => go n xs
  where
  go : Nat -> List a -> List a   
  go  Z    xs = xs
  go (S n) xs = x :: go n xs 

public export
foldr : (a -> b -> b) -> b -> DList a -> b
foldr f b = foldr f b . toList

public export
Semigroup (DList a) where
  (<+>) = (++)

public export
Monoid (DList a) where
  neutral = nil

public export
Functor DList where
  map f = DList.foldr (cons . f) nil
