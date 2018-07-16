module TParsec.Types

import public Control.Monad.State
import Relation.Subset
import Relation.Indexed
import Data.Inspect
import TParsec.Success
import TParsec.Result

%default total
%access public export

-- Helpers

mapFst : (a -> c) -> (a, b) -> (c, b)
mapFst f (a, b) = (f a, b)

mapSnd : (b -> c) -> (a, b) -> (a, c)
mapSnd f (a, b) = (a, f b)

-- Position in the input string

record Position where
  constructor MkPosition
  line : Nat
  offset : Nat

Show Position where
  show (MkPosition line offset) = show line ++ ":" ++ show offset
  
start : Position
start = MkPosition 0 0
  
next : Char -> Position -> Position
next c p = if c == '\n' 
           then MkPosition (S (line p)) 0 
           else record { offset = S (offset p) } p

-- A parser is parametrised by some types and type constructors.

record Parameters (m : Type -> Type) where
  constructor MkParameters
  Tok : Type          -- tokens
  Toks : Nat -> Type  -- sized input (~ Vec Tok)
  -- The action allowing us to track consumed tokens
  recordToken : Tok -> m ()

-- A parser is the ability to, given an input, return a computation for
-- a success.

record Parser (mn : Type -> Type)
              (p : Parameters mn)
              (a : Type) (n : Nat) where
  constructor MkParser
  runParser : {m : Nat} -> LTE m n -> (Toks p) m -> mn (Success (Toks p) a m)  

-- TParsecT

record TParsecT (e : Type) (an : Type) (m : Type -> Type) (a : Type) where  -- error, annotations, monad
  constructor MkTPT 
  runTPT : StateT (Position, List an) (ResultT e m) a

Functor m => Functor (TParsecT e a m) where
  map f (MkTPT a) = MkTPT $ map f a

Monad m => Applicative (TParsecT e a m) where
  pure a = MkTPT $ pure a
  (MkTPT f) <*> (MkTPT a) = MkTPT (f <*> a)

Monad m => Monad (TParsecT e a m) where
  (MkTPT a) >>= f = MkTPT $ a >>= (runTPT . f)

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
withAnnotation a (MkTPT ms) = MkTPT $ do modify (mapSnd (List.(::) a))
                                         s <- ms  
                                         modify (mapSnd (List.drop 1))
                                         pure s

recordChar : Monad m => Char -> TParsecT e a m ()
recordChar c = MkTPT $ ignore (modify (mapFst (next c)))

-- Commiting to a branch makes all the failures in that branch hard failures
-- that we cannot recover from
commitT : Functor m => TParsecT e a m x -> TParsecT e a m x
commitT (MkTPT m) = MkTPT $ ST $ \pos => MkRT $ map (result HardFail HardFail Value) (runResultT $ runStateT m pos)

-- specialized 

chars : Monad m => Parameters (TParsecT e a m)
chars = MkParameters Char (SizedList Char) recordChar

TParsecM : (e : Type) -> (an : Type) -> Type -> Type
TParsecM e an = TParsecT e an Identity

commit : All (Parser (TParsecM e an) p a :-> Parser (TParsecM e an) p a)
commit p = MkParser $ \mlen, ts => commitT $ runParser p mlen ts

TParsecU : Type -> Type
TParsecU = TParsecM () Void

sizedtok : (tok : Type) -> Parameters TParsecU
sizedtok tok = MkParameters tok (SizedList tok) (const $ pure ())  

Subset (Position, List Void) () where
  into = const ()