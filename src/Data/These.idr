module Data.These

%default total

public export
data These a b = This a | That b | Both a b

public export
fromEither : Either a b -> These a b
fromEither = either This That

public export
these : (a -> c) -> (b -> c) -> (a -> b -> c) -> These a b -> c
these l r lr (This a)   = l a
these l r lr (That b)   = r b
these l r lr (Both a b) = lr a b

public export
fromThis : These a b -> Maybe a
fromThis = these Just (const Nothing) (const . Just)

public export
fromThat : These a b -> Maybe b
fromThat = these (const Nothing) Just (const Just)

public export
bimap : (f : a -> b) -> (g : c -> d) -> These a c -> These b d
bimap f g (This a)   = This (f a)
bimap f g (That b)   = That (g b)
bimap f g (Both a b) = Both (f a) (g b)

public export
Functor (These a) where
  map = bimap id

public export
mapFst : (f : a -> b) -> These a c -> These b c
mapFst f = bimap f id

public export
bifold : Monoid m => These m m -> m
bifold (This a)   = a
bifold (That b)   = b
bifold (Both a b) = a <+> b

public export
bitraverse : Applicative f => (a -> f c) -> (b -> f d) -> These a b -> f (These c d)
bitraverse f g (This a)   = This <$> (f a)
bitraverse f g (That b)   = That <$> (g b)
bitraverse f g (Both a b) = Both <$> (f a) <*> (g b)
