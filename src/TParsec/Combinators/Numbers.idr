module TParsec.Combinators.Numbers

import Relation.Indexed
import Relation.Subset
import Data.Inspect
import Data.NEList
import TParsec.Types
import TParsec.Combinators

%default total
%access public export

decimalDigit
  : ( Alternative mn, Monad mn
    , Subset Char (Tok p)
    , Eq (Tok p), Inspect (Toks p) (Tok p)
    ) => All (Parser mn p Nat)
decimalDigit =
  alts $ map (uncurry (\ v, c => cmap v $ exact $ into c))
       [ (0, '0'), (1, '1'), (2, '2'), (3, '3'), (4, '4')
       , (5, '5'), (6, '6'), (7, '7'), (8, '8'), (9, '9') ]

natFromDigits : NEList Nat -> Nat
natFromDigits = foldl (\ih, d => 10 * ih + d) 0

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
decimalDouble =
  let fromNat    = the (Nat -> Double) (fromInteger . cast) in
  let toNat      = the (Integer -> Nat) cast in
  let fractional = rand (exact $ into '.') (box $ nelist decimalDigit) in
  let fromFrac   = \ ds => fromNat (natFromDigits ds) / pow 10 (length ds) in
  let enotation  = rand (alt (exact $ into 'E') (exact $ into 'e')) (box $ decimalInteger) in
  let fromE      = \ e => if e < 0 then (/ pow 10.0 (toNat $ negate e)) else (* pow 10 (toNat e)) in
  let rawdouble  = andopt (andopt decimalInteger fractional) enotation in
  let convert    = \ ((int, mfrac), men) => maybe id fromE men (fromInteger int + maybe 0 fromFrac mfrac)
  in map convert rawdouble
