module Data.Trie

import Data.These
import Data.SortedMap

-- TODO add to SortedMap
public export
mapSingleton : Ord a => a -> b -> SortedMap a b
mapSingleton a b = insert a b empty
--

public export
record Trie a b where
  constructor MkTrie
  node : These b (SortedMap a (Trie a b))

public export
Functor (Trie a) where
  map f (MkTrie node) = MkTrie $ assert_total $ bimap f (map (map f)) node

public export
empty : Ord a => Trie a b
empty = MkTrie $ That empty

public export
singleton : Ord a => List a -> b -> Trie a b
singleton []      v = MkTrie $ This v
singleton (k::ks) v = MkTrie $ That $ mapSingleton k (singleton ks v)

public export
lookup : Ord a => List a -> Trie a b -> Maybe (These b (SortedMap a (Trie a b)))
lookup []        (MkTrie nd) = Just nd
lookup (k :: ks) (MkTrie nd) =
  do ts <- These.fromThat nd
     t  <- SortedMap.lookup k ts
     lookup ks t

public export
lookupValue : Ord a => List a -> Trie a b -> Maybe b
lookupValue ks tr = lookup ks tr >>= fromThis

public export
lookupTries : Ord a => List a -> Trie a b -> Maybe (SortedMap a (Trie a b))
lookupTries ks tr = lookup ks tr >>= fromThat

public export
lookupTrie : Ord a => a -> Trie a b -> Maybe (Trie a b)
lookupTrie k tr = lookupTries [] tr >>= SortedMap.lookup k

public export
insertWith : Ord a => List a -> (Maybe b -> b) -> Trie a b -> Trie a b
insertWith []      f (MkTrie nd) =
  MkTrie $ these (This . f . Just) (Both (f Nothing)) (Both . f . Just) nd
insertWith (k::ks) f (MkTrie nd) =
  MkTrie $ these (\x => Both x (mapSingleton k end)) (That . rec) (\x => Both x . rec) nd
  where
  end : Trie a b
  end = singleton ks (f Nothing)
  rec : SortedMap a (Trie a b) -> SortedMap a (Trie a b)
  rec sm = maybe (insert k end sm) (\tm => insert k (insertWith ks f tm) sm) (lookup k sm)

public export
insert : Ord a => List a -> b -> Trie a b -> Trie a b
insert ks v = insertWith ks (const v)

public export
fromList : Ord a => List (List a, b) -> Trie a b
fromList = foldr (uncurry Trie.insert) empty

public export
foldWithKeysM : (Ord a, Monad m, Monoid c) => (List a -> m c) -> (List a -> b -> m c) -> Trie a b -> m c
foldWithKeysM {a} {m} {c} fk fv = go []
  where
  go : List a -> Trie a b -> m c
  go as (MkTrie nd) =
    bifold <$> bitraverse
                (fv as)
                (\sm => foldlM
                          (\x, (k, vs) => do let as' = as ++ [k]
                                             y <- assert_total $ go as' vs
                                             z <- fk as'
                                             pure $ x <+> y <+> z)
                          neutral
                          (toList sm))
                nd
