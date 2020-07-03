module TParsec.Lexer

import Data.List
import Data.Maybe
import Data.Tuple
import Data.Trie
import public TParsec.Position

%default total

-- Some characters are special: they are separators, breaking a string into
-- a list of tokens. Furthermore, some of the separators are associated to a
-- token value (e.g. parentheses), while others are not (e.g. spaces).
public export
data MaybeBreaking tok = Breaking (Maybe tok) | NotBreaking

public export
record LexParameters where
  constructor MkLexParameters
-- Our lexer is parametrised over the type of tokens
  Tok : Type
-- We start with an association list between
-- * keywords (as Strings)
-- * keywords (as token values)
  keywords : List (String, Tok)
-- We also need to be able to determine which characters are breaking.
  breaking : Char -> MaybeBreaking Tok
-- Finally, strings which are not decoded as keywords are coerced using a
-- function to token values.
  def : String -> Tok

public export
LexResult : LexParameters -> Type
LexResult p = List (Position, Tok p)

-- We build a trie from the association list so that we may easily compute
-- the successive derivatives obtained by eating the characters one by one
public export
Keywords : LexParameters -> Type
Keywords p = Trie Char (Tok p)

public export
init : {p : LexParameters} -> Keywords p
init = Trie.fromList $ map (mapFst unpack) (keywords p)

-- Grab the accumulator and, unless it is empty, push it on top of the
-- decoded list of tokens
public export
push : {p : LexParameters} -> (Position, List Char) -> LexResult p -> LexResult p
push (pos, []) ts = ts
push (pos, cs) ts = (pos, def p (pack (reverse cs))) :: ts

-- The action corresponding to a breaking character: we only push something
-- if the breaking character is associated to a token
public export
break : Position -> Maybe (Tok p) -> LexResult p -> LexResult p
break pos (Just tok) rs = (pos, tok) :: rs
break pos  Nothing   rs = rs

public export
read : {p : LexParameters} -> Char -> Keywords p -> Keywords p
read t ks = fromMaybe empty $ lookupTrie t ks

public export
value : Keywords p -> Maybe (Tok p)
value = lookupValue []

mutual
  -- Kickstart the tokeniser with an empty accumulator and the initial trie.
  public export
  start : {p : LexParameters} -> Position -> List Char -> LexResult p
  start pos = loop (pos, []) init pos

  -- The main loop
  public export
  loop : {p : LexParameters} ->
         (acc  : (Position, List Char)) -> -- start position & chars read so far in this token
         (toks : Keywords p)            -> -- keyword candidates left at this point
         (pos : Position)               -> -- current position in the input string
         (input : List Char)            -> -- list of chars to tokenize
         LexResult p
  -- Empty input: finish up, check whether we have a non-empty accumulator
  loop     acc toks pos []        = push acc []
  -- At least one character
  loop {p} acc toks pos (c :: cs) = case breaking p c of
    -- if we are supposed to break on this character, we do
    Breaking m  => push acc $ break pos m $ assert_total $ start (Position.update c pos) cs
    -- otherwise we see whether it leads to a recognized keyword
    NotBreaking => let toks' = read c toks in
               case value toks' of
    -- if so we can forget about the current accumulator and restart
    -- the tokenizer on the rest of the input
                 Just tok => (fst acc, tok) :: (assert_total $ start (Position.update c pos) cs)
    -- otherwise we record the character we read in the accumulator,
    -- compute the derivative of the map of keyword candidates and keep
    -- going with the rest of the input
                 Nothing  => loop (mapSnd (c::) acc) toks' (Position.update c pos) cs

public export
tokenize : {p : LexParameters} -> String -> LexResult p
tokenize = start Position.start . unpack
