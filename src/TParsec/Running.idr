module TParsec.Running

import TParsec.Indexed
import TParsec.Success
import TParsec.Combinators
import TParsec.Inspect

%default total
%access public export

data Singleton : a -> Type where
  MkSingleton : (v : a) -> Singleton v

interface Tokenizer (tok : Type) where
  tokenize : String -> List tok

implementation Tokenizer Char where
  tokenize = unpack

interface MonadRun (mn : Type -> Type) where
  runMonad : mn a -> List a

implementation MonadRun List where
  runMonad = id

implementation MonadRun Maybe where
  runMonad = lowerMaybe . map pure

parse : (Tokenizer tok, MonadRun mn) =>
        String -> (All (Parser (SizedList tok) tok mn a)) -> Type
parse str p =
  let tokens = tokenize str in
  let input  = MkSizedList tokens in
  let result = runParser p lteRefl input in
  let valid  = \ s => if Size s == Z then Just (Value s) else Nothing in
  case traverse valid (runMonad result) of
    Just (hd :: _) => Singleton hd
    _              => Void
