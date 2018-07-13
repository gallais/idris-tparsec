module TParsec.Running

import Relation.Indexed
import Data.Inspect
import TParsec.Success
import TParsec.Result
import TParsec.Types
import TParsec.Combinators

%default total
%access public export

data Singleton : a -> Type where
  MkSingleton : (v : a) -> Singleton v

interface Tokenizer (tok : Type) where
  tokenize : String -> List tok

Tokenizer Char where
  tokenize = unpack
  
interface SizedInput (tok : Type) (toks : Nat -> Type) where
  sizedInput : (ts : List tok) -> toks (length ts)

SizedInput a (SizedList a) where
  sizedInput = MkSizedList

interface MonadRun (mn : Type -> Type) where
  runMonad : mn a -> List a

MonadRun List where
  runMonad = id

MonadRun Maybe where
  runMonad = lowerMaybe . map pure

MonadRun Identity where
  runMonad (Id a) = pure a

MonadRun m => MonadRun (ResultT e m) where
  runMonad (MkRT r) = runMonad r >>= result (const []) (const []) pure

MonadRun m => MonadRun (TParsecT e a m) where
  runMonad (MkTPT r) = map fst $ runMonad $ runStateT r (start, [])

parseMaybe : (MonadRun mn, Tokenizer (Tok p), SizedInput (Tok p) (Toks p)) =>
             String -> (All (Parser mn p a)) -> Maybe a
parseMaybe {p} str par =
  let 
    input  = sizedInput {tok = Tok p} {toks = Toks p} $ tokenize {tok = Tok p} str 
    result = runParser par lteRefl input
    valid  = \s => toMaybe (Size s == Z) (Value s)
    in
  traverse valid (runMonad result) >>= head'

parseType : (MonadRun mn, Tokenizer (Tok p), SizedInput (Tok p) (Toks p)) =>
        String -> (All (Parser mn p a)) -> Type
parseType str par = maybe Void Singleton $ parseMaybe str par

parseResult : (Tokenizer (Tok p), SizedInput (Tok p) (Toks p)) => 
              String -> All (Parser (TParsecM e an) p a) -> Result e a
parseResult {p} str par =  
  let 
    input  = sizedInput {tok = Tok p} {toks = Toks p} $ tokenize {tok = Tok p} str 
    st = runParser par lteRefl input
    res = runIdentity $ runResultT $ runStateT (runTPT st) (start, []) 
    in 
  map (Success.Value . fst) res
