module TParsec.Types

import public Control.Monad.State
import public Control.Monad.Trans
import Relation.Subset
import Relation.Indexed
import Data.Tuple
import Data.Inspect
import TParsec.Success
import TParsec.Result
import TParsec.Position

%default total
%access public export
%hide Stream.(::)

||| A parser is parametrised by some types and type constructors.
||| They are grouped in a `Parameters` record.
||| @ m is the monad the parser uses.
record Parameters (m : Type -> Type) where
  constructor MkParameters
  ||| Type of tokens
  Tok : Type
  ||| Type of sized input (~ Vec Tok)
  Toks : Nat -> Type
  ||| The action allowing us to track consumed tokens
  recordToken : Tok -> m ()

||| A parser is the ability to, given an input, return a computation for
||| a success.
||| @ mn the monad used for parsing
||| @ p the parameters
||| @ a the type of value produced
||| @ n an upper bound on the size of the inputs it can deal with
record Parser (mn : Type -> Type)
              (p : Parameters mn)
              (a : Type)
              (n : Nat) where
  constructor MkParser
  runParser : {m : Nat} -> LTE m n -> (Toks p) m -> mn (Success (Toks p) a m)

||| `TParsecT` is the monad transformer one would typically use when defining
||| an instrumented parser
||| @ e the errors the parser may raise
||| @ an the annotations the user can put on subparses
||| @ m the monad the transformer acts upon
||| @ a the type of values it returns
record TParsecT (e : Type) (an : Type) (m : Type -> Type) (a : Type) where
  constructor MkTPT
  runTPT : StateT (Position, List an) (ResultT e m) a

Functor m => Functor (TParsecT e a m) where
  map f (MkTPT a) = MkTPT $ map f a

Monad m => Applicative (TParsecT e a m) where
  pure a = MkTPT $ pure a
  (MkTPT f) <*> (MkTPT a) = MkTPT (f <*> a)

Monad m => Monad (TParsecT e a m) where
  (MkTPT a) >>= f = MkTPT $ a >>= (runTPT . f)

MonadTrans (TParsecT e a) where
  lift = MkTPT . lift . lift

||| The `Alternative` instance recovers from "soft" failures in the left branch
||| by exploring the right one. "hard" failures are final.
(Monad m, Subset (Position, List a) e) => Alternative (TParsecT e a m) where
  empty = MkTPT $ ST $ MkRT . pure . SoftFail . into
  (MkTPT a) <|> (MkTPT b) = MkTPT $ ST $ \pos =>
    MkRT $ (runResultT $ runStateT a pos) >>= (\r => case r of
      SoftFail _ => runResultT $ runStateT b pos
      _ => pure r)

getPosition : Monad m => TParsecT e a m Position
getPosition = MkTPT $ map Basics.fst get

getAnnotations : Monad m => TParsecT e a m (List a)
getAnnotations = MkTPT $ map Basics.snd get

withAnnotation : Monad m => a -> TParsecT e a m x -> TParsecT e a m x
withAnnotation a (MkTPT ms) = MkTPT $ do modify $ Functor.map (a ::)
                                         s <- ms
                                         modify $ Functor.map (List.drop 1)
                                         pure s

recordChar : Monad m => Char -> TParsecT e a m ()
recordChar c = MkTPT $ ignore (modify (mapFst (update c)))
  where
  mapFst : (x -> y) -> (x, z) -> (y, z)
  mapFst f (x, z) = (f x, z)

||| Commiting to a branch makes all the failures in that branch hard failures
||| that we cannot recover from
commitT : Functor m => TParsecT e a m x -> TParsecT e a m x
commitT (MkTPT m) = MkTPT $ ST $ \pos =>
   MkRT $ map (result HardFail HardFail Value) (runResultT $ runStateT m pos)

commit : Functor mn => All (Parser (TParsecT e an mn) p a :-> Parser (TParsecT e an mn) p a)
commit p = MkParser $ \mlen, ts => commitT $ runParser p mlen ts

||| Specialized versions of `Parameters` and `TParsecT` for common use cases

chars : Monad m => Parameters (TParsecT e a m)
chars = MkParameters Char (SizedList Char) recordChar

TParsecM : (e : Type) -> (an : Type) -> Type -> Type
TParsecM e an = TParsecT e an Identity

TParsecU : Type -> Type
TParsecU = TParsecM () Void

sizedtok : (tok : Type) -> Parameters TParsecU
sizedtok tok = MkParameters tok (SizedList tok) (const $ pure ())

Subset (Position, List Void) () where
  into = const ()
