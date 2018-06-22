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

parseMaybe : (Tokenizer tok, MonadRun mn) =>
        String -> (All (Parser (SizedList tok) tok mn a)) -> Maybe a
parseMaybe str p =
  let 
    tokens = tokenize str 
    input  = MkSizedList tokens
    result = runParser p lteRefl input
    valid  = \ s => if Size s == Z then Just (Value s) else Nothing
    in
  traverse valid (runMonad result) >>= head'

parse : (Tokenizer tok, MonadRun mn) =>
        String -> (All (Parser (SizedList tok) tok mn a)) -> Type
parse str p = maybe Void Singleton $ parseMaybe str p
