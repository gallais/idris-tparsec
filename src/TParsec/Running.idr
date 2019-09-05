module TParsec.Running

import Relation.Indexed
import Data.Inspect
import TParsec.Position
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

interface Pointed (a : Type) where
  point : a

(MonadRun m, Pointed s) => MonadRun (StateT s m) where
  runMonad st = map fst $ runMonad $ runStateT st point

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
   in
  head' $ mapMaybe complete $ runMonad result

parseType : (MonadRun mn, Tokenizer (Tok p), SizedInput (Tok p) (Toks p)) =>
            String -> (All (Parser mn p a)) -> Type
parseType str par = maybe Void Singleton $ parseMaybe str par

parseResults : (MonadRun mn, Tokenizer (Tok p), SizedInput (Tok p) (Toks p)) => 
               String -> All (Parser (TParsecT e an mn) p a) -> Result e (List a)
parseResults {p} str par =  
  let 
    input  = sizedInput {tok = Tok p} {toks = Toks p} $ tokenize {tok = Tok p} str 
    st = runParser par lteRefl input
    res = sequence $ runMonad $ runResultT $ runStateT (runTPT st) (start, []) 
   in
  map (mapMaybe $ complete . fst) res

parseResult : (MonadRun mn, Tokenizer (Tok p), SizedInput (Tok p) (Toks p)) => 
              String -> All (Parser (TParsecT e an mn) p a) -> Result e (Maybe a)
parseResult str par = map head' $ parseResults str par
