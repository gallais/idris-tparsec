module TParsec.NEList

%default total
%access public export

record NEList (a : Type) where
  constructor MkNEList
  head : a
  tail : List a

toList : NEList a -> List a
toList xxs = head xxs :: tail xxs

Show a => Show (NEList a) where
  show = show . toList

fromList : List a -> Maybe (NEList a)
fromList []        = Nothing
fromList (x :: xs) = Just (MkNEList x xs)

consm : a -> Maybe (NEList a) -> NEList a
consm x mxs = MkNEList x (lowerMaybe (map toList mxs))

cons : a -> NEList a -> NEList a
cons x xxs = MkNEList x (toList xxs)

singleton : a -> NEList a
singleton x = MkNEList x []

Foldable NEList where
  foldl c n xxs = foldl c n (NEList.toList xxs)
  foldr c n xxs = foldr c n (NEList.toList xxs)

foldl1 : (a -> a -> a) -> NEList a -> a
foldl1 c (MkNEList x xs) = foldl c x xs

foldr1 : (a -> a -> a) -> NEList a -> a
foldr1 c (MkNEList x xs) = go x xs where

  go : a -> List a -> a
  go x []        = x
  go x (y :: ys) = c x (go y ys)

foldrf : (a -> b -> b) -> (a -> b) -> NEList a -> b
foldrf c s (MkNEList x xs) = go x xs 
  where
  go x [] = s x
  go x (y :: ys) = c x (go y ys)

Functor NEList where
  map f (MkNEList x xs) = MkNEList (f x) (Functor.map f xs)

Semigroup (NEList a) where
  (MkNEList x xs) <+> ys = MkNEList x (xs ++ NEList.toList ys)
