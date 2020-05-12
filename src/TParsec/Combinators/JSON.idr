module TParsec.Combinators.JSON

import Relation.Indexed
import Relation.Subset
import Data.Inspect
import Data.NEList as NEList
import Induction.Nat as Box
import TParsec.Types
import TParsec.Combinators
import TParsec.Combinators.Chars
import TParsec.Combinators.Numbers
import Language.JSON.Data

%default total
%access public export

--- We follow the following RFC:
-- https://tools.ietf.org/html/rfc7158

-- In this parser we assume that when we call a subparser all of the whitespace
-- before the potential token has been consumed already. That means that we should
-- systematically consume spaces after the tokens we have happily recognised.

-- Structural characters

beginArray
  : ( Monad mn, Alternative mn
    , Inspect (Toks p) (Tok p), Eq (Tok p)
    , Subset Char (Tok p)
    ) => All (Parser mn p ())
beginArray = cmap () $ andopt (char '[') spaces

beginObject
  : ( Monad mn, Alternative mn
    , Inspect (Toks p) (Tok p), Eq (Tok p)
    , Subset Char (Tok p)
    ) => All (Parser mn p ())
beginObject = cmap () $ andopt (char '{') spaces

endArray
  : ( Monad mn, Alternative mn
    , Inspect (Toks p) (Tok p), Eq (Tok p)
    , Subset Char (Tok p)
    ) => All (Parser mn p ())
endArray = cmap () $ andopt (char ']') spaces

endObject
  : ( Monad mn, Alternative mn
    , Inspect (Toks p) (Tok p), Eq (Tok p)
    , Subset Char (Tok p)
    ) => All (Parser mn p ())
endObject = cmap () $ andopt (char '}') spaces

nameSeparator
  : ( Monad mn, Alternative mn
    , Inspect (Toks p) (Tok p), Eq (Tok p)
    , Subset Char (Tok p)
    ) => All (Parser mn p ())
nameSeparator = cmap () $ andopt (char ':') spaces

valueSeparator
  : ( Monad mn, Alternative mn
    , Inspect (Toks p) (Tok p), Eq (Tok p)
    , Subset Char (Tok p)
    ) => All (Parser mn p ())
valueSeparator = cmap () $ andopt (char ',') spaces

||| A string literal is an opening and a closing double quote with
||| a chain of non-empty lists of characters that are neither a
||| double quote nor an escaping character.
||| This chain is separated by non-empty lists of blocks made of
||| an escaping character and its escapee.
||| Additionally, there may be another such block of escapees on
||| each side of the chain.
stringLiteral
  : ( Monad mn, Alternative mn
    , Inspect (Toks p) (Tok p), Eq (Tok p)
    , Subset Char (Tok p), Subset (Tok p) Char
    ) => All (Parser mn p String)
stringLiteral {mn} {p}
  = map (fromMaybe "")
  $ rand (char '"') $ box $ flip loptand (char '"')
  $ map (pack . toList . map into)
  $ innerString

  where

    toks : Type
    toks = NEList (Tok p)

    unescaped : All (Parser mn p toks)
    unescaped = nelist (noneOfChars ['\\','"'])

    escaped : All (Parser mn p toks)
    escaped = nelist (rand (char '\\') (box anyTok))

    escapees : All (Parser mn p (toks -> toks -> toks))
    escapees = map {b = toks -> toks -> toks}
                   (\ t => \ bef, aft => bef ++ t ++ aft) escaped

    innerString : All (Parser mn p toks)
    innerString = map (\ (mpre, str, mpost) => optappend mpre (appendopt str mpost))
                $ optand escaped
                $ andopt (chainr1 unescaped (box escapees))
                $ box escaped

member
  : ( Monad mn, Alternative mn
    , Inspect (Toks p) (Tok p), Eq (Tok p)
    , Subset Char (Tok p), Subset (Tok p) Char
    ) => All (Box (Parser mn p JSON) :-> Parser mn p (String, JSON))
member rec
  = and (landopt stringLiteral spaces)
  $ rand nameSeparator
  $ rec

object
  : ( Monad mn, Alternative mn
    , Inspect (Toks p) (Tok p), Eq (Tok p)
    , Subset Char (Tok p), Subset (Tok p) Char
    ) => All (Box (Parser mn p JSON) :-> Parser mn p (List (String, JSON)))
object rec
  = map (maybe [] (\ (a, as) => NEList.toList (consopt a as)))
  $ flip land endObject
  $ randopt beginObject
  $ box $ andopt (member rec)
  $ nelist (rand valueSeparator (member rec))


array
  : ( Monad mn, Alternative mn
    , Inspect (Toks p) (Tok p), Eq (Tok p)
    , Subset Char (Tok p)
    ) => All (Box (Parser mn p JSON) :-> Parser mn p (List JSON))
array rec
  = map (maybe [] (\ (a, as) => NEList.toList (consopt a as)))
  $ flip land endArray
  $ randopt beginArray
  $ lift2l (\ p, q => andopt p (box q)) rec
  $ nelist (rand valueSeparator rec)

||| Parsing JSON values
value
  : ( Monad mn, Alternative mn
    , Inspect (Toks p) (Tok p), Eq (Tok p)
    , Subset Char (Tok p), Subset (Tok p) Char
    ) => All (Parser mn p JSON)
value {mn} {p} = roptand spaces $ fix (Parser mn p JSON) $ \ rec => alts
  [ cmap JNull            (landopt (string "null") spaces)
  , cmap (JBoolean True)  (landopt (string "true") spaces)
  , cmap (JBoolean False) (landopt (string "false") spaces)
  , map  JNumber          (landopt decimalDouble spaces)
  , map  JString          (landopt stringLiteral spaces)
  , map  JArray           (array rec)
  , map  JObject          (object rec)
  ]
