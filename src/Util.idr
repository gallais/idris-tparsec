module Util

%default total

public export
singleton : Char -> String
singleton c = strCons c ""
