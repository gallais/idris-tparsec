module Data.Tuple

%default total

public export
mapSnd : (b -> c) -> (a, b) -> (a, c)
mapSnd f (a, b) = (a, f b)
