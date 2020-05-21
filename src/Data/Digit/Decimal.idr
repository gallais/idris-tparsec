module Data.Digit.Decimal

import Data.So

%default total
%access public export

record Dec where
  constructor MkDec
  toNat : Nat
  bound : So (lt toNat 10)

mkDec : (d : Nat) -> {auto pr : So (lt d 10)} -> Dec
mkDec d {pr} = MkDec d pr

toChar : Dec -> Char
toChar = assert_total $ flip strIndex 0 . show . toNat

