module Data.NEList

import Data.List
import Data.Vect

%default total

public export
record NEList (a : Type) where
  constructor MkNEList
  head : a
  tail : List a

public export
toList : NEList a -> List a
toList xxs = head xxs :: tail xxs

public export
length : NEList a -> Nat
length = S . length . tail

public export
toVect : (nel : NEList a) -> Vect (length nel) a
toVect (MkNEList h t) = h :: fromList t

public export
Show a => Show (NEList a) where
  show = show . NEList.toList

public export
fromList : List a -> Maybe (NEList a)
fromList []        = Nothing
fromList (x :: xs) = Just (MkNEList x xs)

public export
consopt : a -> Maybe (NEList a) -> NEList a
consopt x mxs = MkNEList x (lowerMaybe (map NEList.toList mxs))

public export
cons : a -> NEList a -> NEList a
cons x xxs = MkNEList x (NEList.toList xxs)

public export
singleton : a -> NEList a
singleton x = MkNEList x []

public export
(++) : NEList a -> NEList a -> NEList a
(++) (MkNEList x xs) ys = MkNEList x (xs ++ NEList.toList ys)

public export
Eq a => Eq (NEList a) where
  (MkNEList x xs) == (MkNEList y ys) = x == y && xs == ys

public export
Semigroup (NEList a) where
   (<+>) = (++)

public export
Functor NEList where
  map f (MkNEList x xs) = MkNEList (f x) (f <$> xs)

public export
Applicative NEList where
  pure = singleton
  (MkNEList f fs) <*> (MkNEList x xs) = MkNEList (f x) ((f <$> xs) ++ (fs <*> (x::xs)))

public export
Monad NEList where
  (MkNEList x xs) >>= f =
    let
      MkNEList y ys = f x
      zs = xs >>= NEList.toList . f
     in
    MkNEList y (ys ++ zs)

public export
Foldable NEList where
  foldl c n xxs = foldl c n (NEList.toList xxs)
  foldr c n xxs = foldr c n (NEList.toList xxs)

public export
foldl1 : (a -> a -> a) -> NEList a -> a
foldl1 c (MkNEList x xs) = foldl c x xs

public export
foldr1 : (a -> a -> a) -> NEList a -> a
foldr1 c (MkNEList x xs) = go x xs
  where
  go : a -> List a -> a
  go x []        = x
  go x (y :: ys) = c x (go y ys)

public export
foldrf : (a -> b -> b) -> (a -> b) -> NEList a -> b
foldrf c s (MkNEList x xs) = go x xs
  where
  go : a -> List a -> b
  go x [] = s x
  go x (y :: ys) = c x (go y ys)

public export
Traversable NEList where
  traverse f (MkNEList x xs) = MkNEList <$> (f x) <*> (traverse f xs)
