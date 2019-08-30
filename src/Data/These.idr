module Data.These

%access public export
%default total

data These a b = This a | That b | Both a b 

fromEither : Either a b -> These a b
fromEither = either This That

these : (a -> c) -> (b -> c) -> (a -> b -> c) -> These a b -> c
these l r lr (This a)   = l a
these l r lr (That b)   = r b
these l r lr (Both a b) = lr a b

fromThis : These a b -> Maybe a
fromThis = these Just (const Nothing) (const . Just)

fromThat : These a b -> Maybe b
fromThat = these (const Nothing) Just (const Just)

bimap : (f : a -> b) -> (g : c -> d) -> These a c -> These b d
bimap f g (This a)   = This (f a)
bimap f g (That b)   = That (g b)
bimap f g (Both a b) = Both (f a) (g b)

Functor (These a) where
  map = bimap id

mapFst : (f : a -> b) -> These a c -> These b c
mapFst f = bimap f id

bifold : Monoid m => These m m -> m
bifold (This a)   = a
bifold (That b)   = b 
bifold (Both a b) = a <+> b

bitraverse : Applicative f => (a -> f c) -> (b -> f d) -> These a b -> f (These c d)
bitraverse f g (This a)   = [| This (f a) |] 
bitraverse f g (That b)   = [| That (g b) |]
bitraverse f g (Both a b) = [| Both (f a) (g b) |]
