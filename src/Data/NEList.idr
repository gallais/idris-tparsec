module Data.NEList

import Data.Vect

%default total
%access public export

record NEList (a : Type) where
  constructor MkNEList
  head : a
  tail : List a

toList : NEList a -> List a
toList xxs = head xxs :: tail xxs

fromList : List a -> Maybe (NEList a)
fromList []        = Nothing
fromList (x :: xs) = Just (MkNEList x xs)

length : NEList a -> Nat
length = S . length . tail

toVect : (nel : NEList a) -> Vect (length nel) a
toVect (MkNEList h t) = h :: Vect.fromList t

cons : a -> NEList a -> NEList a
cons x xxs = MkNEList x (toList xxs)

consopt : a -> Maybe (NEList a) -> NEList a
consopt x mxs = MkNEList x (lowerMaybe (map toList mxs))

singleton : a -> NEList a
singleton x = MkNEList x []

(++) : NEList a -> NEList a -> NEList a
(++) (MkNEList x xs) ys = MkNEList x (xs ++ NEList.toList ys)

optappend : Maybe (NEList a) -> NEList a -> NEList a
optappend ml = maybe id (++) ml

appendopt : NEList a -> Maybe (NEList a) -> NEList a
appendopt l mr = maybe l (l ++) mr

Show a => Show (NEList a) where
  show = show . toList

Eq a => Eq (NEList a) where
  (MkNEList x xs) == (MkNEList y ys) = x == y && xs == ys

Semigroup (NEList a) where
   (<+>) = (++)

Functor NEList where
  map f (MkNEList x xs) = MkNEList (f x) (f <$> xs)

Applicative NEList where
  pure = singleton
  (MkNEList f fs) <*> (MkNEList x xs) = MkNEList (f x) ((f <$> xs) ++ (fs <*> (x::xs)))

Monad NEList where
  (MkNEList x xs) >>= f =
    let
      MkNEList y ys = f x
      zs = xs >>= toList . f
     in
    MkNEList y (ys ++ zs)

Foldable NEList where
  foldl c n xxs = foldl c n (NEList.toList xxs)
  foldr c n xxs = foldr c n (NEList.toList xxs)

foldl1 : (a -> a -> a) -> NEList a -> a
foldl1 c (MkNEList x xs) = foldl c x xs

foldr1 : (a -> a -> a) -> NEList a -> a
foldr1 c (MkNEList x xs) = go x xs
  where
  go : a -> List a -> a
  go x []        = x
  go x (y :: ys) = c x (go y ys)

foldrf : (a -> b -> b) -> (a -> b) -> NEList a -> b
foldrf c s (MkNEList x xs) = go x xs
  where
  go x []        = s x
  go x (y :: ys) = c x (go y ys)

Traversable NEList where
  traverse f (MkNEList x xs) = [| MkNEList (f x) (traverse f xs) |]
