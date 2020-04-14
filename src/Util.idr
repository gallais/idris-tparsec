module Util

public export
singleton : Char -> String
singleton c = strCons c ""

public export
head' : List a -> Maybe a
head' []      = Nothing
head' (x::xs) = Just x
