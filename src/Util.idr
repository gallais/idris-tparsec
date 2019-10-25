module Util

public export
singleton : Char -> String
singleton c = strCons c ""

public export
head' : List a -> Maybe a
head' []      = Nothing
head' (x::xs) = Just x

public export
ignore : Functor f => f a -> f ()
ignore = map (const ())

public export
Functor (Pair a) where
  map f (x, y) = (x, f y)

public export
choice : (Foldable t, Alternative f) => t (f a) -> f a
choice = foldr (<|>) empty

public export
choiceMap : (Foldable t, Alternative f) => (a -> f b) -> t a -> f b
choiceMap f = foldr (\e, a => f e <|> a) empty
