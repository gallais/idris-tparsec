module Data.Tuple

%default total
%access public export

mapFst : (a -> c) -> (a, b) -> (c, b)
mapFst f (a, b) = (f a, b)

mapSnd : (b -> c) -> (a, b) -> (a, c)
mapSnd f (a, b) = (a, f b)