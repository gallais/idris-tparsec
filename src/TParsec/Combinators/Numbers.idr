module TParsec.Combinators.Numbers

import Util
import Relation.Indexed
import Relation.Subset
import Data.Inspect
import Data.NEList
import TParsec.Types
import TParsec.Combinators

public export
decimalDigit : {p : Parameters mn} ->
               (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
               All (Parser mn p Nat)
decimalDigit =
  alts $ map (uncurry (\ v, c => cmap v $ exact $ into c))
       [ (0, '0'), (1, '1'), (2, '2'), (3, '3'), (4, '4')
       , (5, '5'), (6, '6'), (7, '7'), (8, '8'), (9, '9') ]

public export
decimalNat : {p : Parameters mn} ->
             (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
             All (Parser mn p Nat)
decimalNat =
  let convert = foldl (\ih, d => 10 * ih + d) 0 in
  Combinators.map convert (nelist decimalDigit)

public export
decimalInteger : {p : Parameters mn} ->
                 (Alternative mn, Monad mn, Subset Char (Tok p), Eq (Tok p), Inspect (Toks p) (Tok p)) =>
                 All (Parser mn p Integer)
decimalInteger =
  let convert = \s, v => maybe {a=Tok p} id (\ _ => negate) s (natToInteger v) in
  Combinators.map (uncurry convert) (optand (exact $ into '-') decimalNat)