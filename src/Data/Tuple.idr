module Data.Tuple

public export
mapFst : (a -> c) -> (a, b) -> (c, b)
mapFst f (a, b) = (f a, b)

public export
mapSnd : (b -> c) -> (a, b) -> (a, c)
mapSnd f (a, b) = (a, f b)
