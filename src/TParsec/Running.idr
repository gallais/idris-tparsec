module TParsec.Running

import Relation.Indexed
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

interface SizedInput (tok : Type) (toks : Nat -> Type) where
  sizedInput : (ts : List tok) -> toks (length ts)

Tokenizer Char where
  tokenize = unpack

SizedInput Char (SizedList Char) where
  sizedInput = MkSizedList

interface MonadRun (mn : Type -> Type) where
  runMonad : mn a -> List a

MonadRun List where
  runMonad = id

MonadRun Maybe where
  runMonad = lowerMaybe . map pure

parseMaybe : (MonadRun mn, Instrumented p mn, Tokenizer (Tok p), SizedInput (Tok p) (Toks p)) =>
             String -> (All (Parser p mn a)) -> Maybe a
parseMaybe {p} str par =
  let 
    input  = sizedInput {tok = Tok p} {toks = Toks p} $ tokenize {tok = Tok p} str 
    result = runParser par lteRefl input
    valid  = \s => toMaybe (Size s == Z) (Value s)
    in
  traverse valid (runMonad result) >>= head'

parse : (MonadRun mn, Instrumented p mn, Tokenizer (Tok p), SizedInput (Tok p) (Toks p)) =>
        String -> (All (Parser p mn a)) -> Type
parse str par = maybe Void Singleton $ parseMaybe str par
