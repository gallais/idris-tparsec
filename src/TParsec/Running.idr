module TParsec.Running

import Relation.Indexed
import Relation.Subset
import Data.Inspect
import TParsec.Success
import TParsec.Types
import TParsec.Instruments
import TParsec.Combinators

%default total
%access public export

data Singleton : a -> Type where
  MkSingleton : (v : a) -> Singleton v

interface Tokenizer (tok : Type) where
  tokenize : String -> List tok

Tokenizer Char where
  tokenize = unpack

interface MonadRun (mn : Type -> Type) where
  runMonad : mn a -> List a

MonadRun List where
  runMonad = id

MonadRun Maybe where
  runMonad = lowerMaybe . map pure

parseMaybe : (str : String) -> (MonadRun mn, Instrumented p mn, Tokenizer (Tok p), Subset (SizedList (Tok p) (length $ tokenize {tok = Tok p} str)) (Toks p n)) =>
             (All (Parser p mn a)) -> Maybe a
parseMaybe @{str} @{mr} @{is} @{to} @{su} par =
  let 
    input = MkSizedList $ tokenize @{to} str 
    result = runParser par lteRefl (into @{su} input)
    valid  = \s => toMaybe (Size s == Z) (Value s)
    in
  traverse valid (runMonad result) >>= head'
{-
parse : (MonadRun mn, Instrumented p mn, Tokenizer (Tok p) (SizedList (Tok p))) =>
        String -> (All (Parser p mn a)) -> Type
parse str par = maybe Void Singleton $ parseMaybe str par
    -}