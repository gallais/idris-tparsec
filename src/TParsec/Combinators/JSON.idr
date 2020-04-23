module TParsec.Combinators.JSON

import Relation.Indexed
import Relation.Subset
import Data.Inspect
import Data.NEList as NEList
import Induction.Nat as Box
import TParsec.Types
import TParsec.Combinators
import TParsec.Combinators.Chars
import Language.JSON.Data

%default total


||| A string literal is an opening and a closing double quote with
||| a chain of non-empty lists of characters that are neither a
||| double quote nor an escaping character.
||| This chain is separated by groups of an escaping character and
||| its escapee.
stringLiteral
  : ( Monad mn, Alternative mn
    , Inspect (Toks p) (Tok p), Eq (Tok p)
    , Subset Char (Tok p), Subset (Tok p) Char
    ) => All (Parser mn p String)
stringLiteral
  = map (fromMaybe "")
  $ rand (char '"') $ box $ flip loptand (char '"')
  $ map (pack . toList . map into)
  $ chainr1 (nelist (noneOfChars ['\\','"']))
                 (cmap (++) (and (char '\\') (box anyTok)))

jsonArray
  : ( Monad mn, Alternative mn
    , Inspect (Toks p) (Tok p), Eq (Tok p)
    , Subset Char (Tok p)
    ) => All (Box (Parser mn p JSON) :-> Parser mn p (List JSON))
jsonArray rec
  = flip alt (cmap [] $ string "[]")
  $ map (NEList.toList . uncurry consopt)
  $ andopt (rand (char '[') rec) (box $ nelist (rand (char ',') rec))
-- NB: it is theoretically possible to parse the opening bracket first
-- and then optionally parse a non-empty list of JSON values before
-- parsing the closing bracket.
-- This is however much more simple to write.


||| Parsing JSON
json
  : ( Monad mn, Alternative mn
    , Inspect (Toks p) (Tok p), Eq (Tok p)
    , Subset Char (Tok p), Subset (Tok p) Char
    ) => All (Parser mn p JSON)
json = fix (Parser _ _ JSON) $ \ rec => roptand spaces $ alts
  [ cmap JNull            (string "null")
  , cmap (JBoolean True)  (string "true")
  , cmap (JBoolean False) (string "false")
  , ?number
  , map  JString          stringLiteral
  , map  JArray           (jsonArray rec)
  , ?object
  ]

{-
   | JNumber Double
   | JArray (List JSON)
   | JObject (List (String, JSON))
-}
