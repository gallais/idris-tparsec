module Util

public export
singleton : Char -> String 
singleton c = strCons c ""

public export
mapMaybe : (a -> Maybe b) -> List a -> List b
mapMaybe f []      = []
mapMaybe f (x::xs) =
  case f x of
    Nothing => mapMaybe f xs
    Just j  => j :: mapMaybe f xs

public export
head' : List a -> Maybe a
head' []      = Nothing
head' (x::xs) = Just x

public export
curry : ((a, b) -> c) -> a -> b -> c
curry f a b = f (a, b)

public export
uncurry : (a -> b -> c) -> (a, b) -> c
uncurry f (a, b) = f a b

public export
ignore : Functor f => f a -> f ()
ignore = map (const ())

public export
Functor (Pair a) where
  map f (x, y) = (x, f y)

public export 
mapFst : (p -> r) -> (p, q) -> (r, q)
mapFst f (x, y) = (f x, y)

public export 
choice : (Foldable t, Alternative f) => t (f a) -> f a
choice = foldr (<|>) empty

public export
choiceMap : (Foldable t, Alternative f) => (a -> f b) -> t a -> f b
choiceMap f = foldr (\e, a => f e <|> a) empty
