module TParsec.Combinators.Numbers

import Relation.Indexed
import Relation.Subset
import Data.Digit
import Data.Inspect
import Data.So
import Data.NEList
import TParsec.Types
import TParsec.Combinators

%default total
%access public export

------------------------------------------------------------------------
-- Digits
------------------------------------------------------------------------

binaryDigit
  : ( Alternative mn, Monad mn
    , Subset Char (Tok p)
    , Eq (Tok p), Inspect (Toks p) (Tok p)
    ) => All (Parser mn p Bool)
binaryDigit = alts $ map (\ (v, c) => cmap v $ exact (into c))
              [ (False, '0'), (True, '1') ]

decimalDigit
  : ( Alternative mn, Monad mn
    , Subset Char (Tok p)
    , Eq (Tok p), Inspect (Toks p) (Tok p)
    ) => All (Parser mn p Dec)
decimalDigit =
  alts $ map (uncurry (\ v, c => cmap v $ exact $ into c))
       [ (mkDec 0, '0'), (mkDec 1, '1'), (mkDec 2, '2'), (mkDec 3, '3')
       , (mkDec 4, '4'), (mkDec 5, '5'), (mkDec 6, '6'), (mkDec 7, '7')
       , (mkDec 8, '8'), (mkDec 9, '9') ]

hexadecimalDigit
  : ( Alternative mn, Monad mn
    , Subset Char (Tok p)
    , Eq (Tok p), Inspect (Toks p) (Tok p)
    ) => All (Parser mn p Hex)
hexadecimalDigit
  = alt (map L decimalDigit) $ alts $ map (uncurry (\ v, c => cmap v $ exact (into c)))
    [ (A, 'a'), (B, 'b'), (C, 'c'), (D, 'd'), (E, 'e'), (F, 'f')
    , (A, 'A'), (B, 'B'), (C, 'C'), (D, 'D'), (E, 'E'), (F, 'F')]

------------------------------------------------------------------------
-- Numbers
------------------------------------------------------------------------

natFromDigits : NEList Dec -> Nat
natFromDigits = foldl (\ih, d => 10 * ih + toNat d) 0

decimalNat
  : ( Alternative mn, Monad mn
    , Subset Char (Tok p)
    , Eq (Tok p), Inspect (Toks p) (Tok p)
    ) => All (Parser mn p Nat)
decimalNat = map natFromDigits (nelist decimalDigit)

decimalInteger
  : ( Alternative mn, Monad mn
    , Subset Char (Tok p)
    , Eq (Tok p), Inspect (Toks p) (Tok p)
    ) => All (Parser mn p Integer)
decimalInteger {p} =
  let convert = \s, v => maybe {a=Tok p} id (\ _ => negate) s (toIntegerNat v) in
  Combinators.map (uncurry convert) (optand (exact $ into '-') decimalNat)

decimalDouble
  : ( Alternative mn, Monad mn
    , Subset Char (Tok p)
    , Eq (Tok p), Inspect (Toks p) (Tok p)
    ) => All (Parser mn p Double)
decimalDouble {p} =
  let
    fromNat    = the (Nat -> Double) (fromInteger . cast)
    fractional = rand (exact $ into '.') (box $ nelist decimalDigit)
    fromFrac   = \ ds => fromNat (natFromDigits ds) / pow 10 (length ds)
    enotation  = rand (alt (exact $ into 'E') (exact $ into 'e'))
                      (optand (alt (exact $ into '+') (exact $ into '-')) decimalNat)
    fromE      = the ((Maybe (Tok p), Nat) -> Double -> Double) $
                 \ (ms, e) => if maybe False (== into '-') ms then (/ pow 10.0 e) else (* pow 10.0 e)
    rawdouble  = andopt (andopt decimalInteger fractional) enotation
    convert    = \ ((int, mfrac), men) => maybe id fromE men (fromInteger int + maybe 0 fromFrac mfrac)
   in
  map convert rawdouble
