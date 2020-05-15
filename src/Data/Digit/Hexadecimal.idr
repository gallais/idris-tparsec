module Data.Digit.Hexadecimal

import Data.Digit.Decimal

%default total
%access public export

data Hex : Type where
  L : Dec -> Hex -- L for Lift
  A : Hex
  B : Hex
  C : Hex
  D : Hex
  E : Hex
  F : Hex

toNat : Hex -> Nat
toNat (L d) = toNat d
toNat A     = 10
toNat B     = 11
toNat C     = 12
toNat D     = 13
toNat E     = 14
toNat F     = 15
 
toChar : Hex -> Char
toChar (L d) = toChar d
toChar A     = 'A'
toChar B     = 'B'
toChar C     = 'C'
toChar D     = 'D'
toChar E     = 'E'
toChar F     = 'F'
