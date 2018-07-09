module TParsec.Combinators.Numbers

import Relation.Indexed
import Relation.Subset
import Data.Inspect
import Data.NEList
import TParsec.Types
import TParsec.Instruments
import TParsec.Combinators

%default total
%access public export

decimalDigit : (Alternative mn, Monad mn, Instrumented p mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
               All (Parser p mn Nat)
decimalDigit =
  alts $ map (uncurry (\ v, c => cmap v $ exact $ into c))
       [ (0, '0'), (1, '1'), (2, '2'), (3, '3'), (4, '4')
       , (5, '5'), (6, '6'), (7, '7'), (8, '8'), (9, '9') ]

decimalNat : (Alternative mn, Monad mn, Instrumented p mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
             All (Parser p mn Nat)
decimalNat =
  let convert = foldl (\ih, d => 10 * ih + d) 0 in
  Combinators.map convert (nelist decimalDigit)

decimalInteger : (Alternative mn, Monad mn, Instrumented p mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
                 All (Parser p mn Integer)
decimalInteger {p} =
  let convert = \s, v => maybe {a=Tok p} id (\ _ => negate) s (toIntegerNat v) in
  Combinators.map (uncurry convert) (optand (exact $ into '-') decimalNat)