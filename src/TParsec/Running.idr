module TParsec.Running

import Util
import Data.List
import public Data.Vect
import Data.Maybe
import Data.Nat
import Relation.Indexed
import Data.Inspect
import TParsec.Position
import TParsec.Success
import TParsec.Result
import TParsec.Types
import TParsec.Combinators

%default total

public export
data Singleton : a -> Type where
  MkSingleton : (v : a) -> Singleton v

public export
interface Tokenizer (tok : Type) where
  tokenize : String -> List tok

public export
Tokenizer Char where
  tokenize = unpack

public export
interface SizedInput (tok : Type) (toks : Nat -> Type) where
  sizedInput : (ts : List tok) -> toks (length ts)

public export
SizedInput a (\n => Vect n a) where
  sizedInput = fromList

public export
interface MonadRun (mn : Type -> Type) where
  runMonad : mn a -> List a

public export
MonadRun List where
  runMonad = id

public export
MonadRun Maybe where
  runMonad = lowerMaybe . map pure

public export
MonadRun Identity where
  runMonad (Id a) = pure a

public export
interface Pointed (a : Type) where
  point : a

public export
(MonadRun m, Pointed s) => MonadRun (StateT s m) where
  runMonad st = map fst $ runMonad $ runStateT st point

public export
MonadRun m => MonadRun (ResultT e m) where
  runMonad (MkRT r) = runMonad r >>= result {e} (const []) (const []) pure

public export
MonadRun m => MonadRun (TParsecT e a m) where
  runMonad (MkTPT r) = map fst $ runMonad $ runStateT r (start, [])

public export
parseMaybe : (MonadRun mn, Tokenizer (Tok p), SizedInput (Tok p) (Toks p)) =>
             String -> (All (Parser mn p a)) -> Maybe a
parseMaybe str par =
  let
    input  = sizedInput {tok = Tok p} {toks = Toks p} $ tokenize {tok = Tok p} str
    result = runParser par lteRefl input
   in
  head' $ mapMaybe complete $ runMonad result

public export
parseType : (MonadRun mn, Tokenizer (Tok p), SizedInput (Tok p) (Toks p)) =>
            String -> (All (Parser mn p a)) -> Type
parseType str par = maybe Void Singleton $ parseMaybe str par

public export
parseResults : (MonadRun mn, Tokenizer (Tok p), SizedInput (Tok p) (Toks p)) =>
               String -> All (Parser (TParsecT e an mn) p a) -> Result e (List a)
parseResults str par =
  let
    input  = sizedInput {tok = Tok p} {toks = Toks p} $ tokenize {tok = Tok p} str
    st = runParser par lteRefl input
    res = sequence $ runMonad $ runResultT $ runStateT (runTPT st) (start, [])
   in
  map (mapMaybe $ complete . Builtin.fst) res

public export
parseResult : (MonadRun mn, Tokenizer (Tok p), SizedInput (Tok p) (Toks p)) =>
              String -> All (Parser (TParsecT e an mn) p a) -> Result e (Maybe a)
parseResult str par = map head' $ parseResults str par
