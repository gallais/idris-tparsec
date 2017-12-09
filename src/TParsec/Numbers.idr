module TParsec.Numbers

import TParsec.Indexed
import TParsec.Inspect
import TParsec.Combinators
import TParsec.NEList

%default total
%access public export

decimalDigit : (Inspect toks Char, Monad mn, Alternative mn) =>
               All (Parser toks Char mn Nat)
decimalDigit =
  alts $ map (uncurry (\ v, c => cmap v $ exact c))
       [ (0, '0'), (1, '1'), (2, '2'), (3, '3'), (4, '4')
       , (5, '5'), (6, '6'), (7, '7'), (8, '8'), (9, '9') ]

decimalNat : (Inspect toks Char, Monad mn, Alternative mn) =>
             All (Parser toks Char mn Nat)
decimalNat =
  let convert = foldl (\ ih, d => 10 * ih + d) 0 in
  Combinators.map convert (nelist decimalDigit)

decimalInteger : (Inspect toks Char, Monad mn, Alternative mn) =>
                 All (Parser toks Char mn Integer)
decimalInteger =
  let convert = \ s, v => maybe {a=Char} id (\ _ => negate) s (toIntegerNat v) in
  Combinators.map (uncurry convert) (mand (exact '-') decimalNat)
