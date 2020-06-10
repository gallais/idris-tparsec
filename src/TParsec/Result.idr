module TParsec.Result

import public Control.Monad.Trans

%default total

-- Result

public export
data Result : Type -> Type -> Type where
  HardFail : e -> Result e a
  SoftFail : e -> Result e a
  Value : a -> Result e a

public export
Functor (Result e) where
  map _ (HardFail e) = HardFail e
  map _ (SoftFail e) = SoftFail e
  map f (Value a)    = Value (f a)

public export
Applicative (Result e) where
  pure = Value
  (HardFail e) <*> _ = HardFail e
  (SoftFail e) <*> _ = SoftFail e
  _ <*> (HardFail e) = HardFail e
  _ <*> (SoftFail e) = SoftFail e
  (Value f) <*> (Value a) = Value (f a)

public export
Monad (Result e) where
  (HardFail e) >>= f = HardFail e
  (SoftFail e) >>= f = SoftFail e
  (Value a)    >>= f = f a

public export
(Show a, Show b) => Show (Result a b) where
  show (HardFail e) = "hard fail: " ++ show e
  show (SoftFail e) = "soft fail: " ++ show e
  show (Value a)    = show a

public export
(Eq a, Eq b) => Eq (Result a b) where
  (HardFail e1) == (HardFail e2) = e1 == e2
  (SoftFail e1) == (SoftFail e2) = e1 == e2
  (Value x)     == (Value y)     = x == y
  _             == _             = False  

public export
result : (h, s : e -> b) -> (v : a -> b) -> Result e a -> b
result h _ _ (HardFail e) = h e
result _ s _ (SoftFail e) = s e
result _ _ v (Value a)    = v a

public export
fromMaybe : e -> Maybe a -> Result e a
fromMaybe e = maybe (SoftFail e) Value

public export
record ResultT (e : Type) (m : Type -> Type) (a : Type) where
  constructor MkRT
  runResultT : m (Result e a)

public export
Functor m => Functor (ResultT e m) where
  map f (MkRT fr) = MkRT $ map (map f) fr

public export
Monad m => Applicative (ResultT e m) where
  pure a = MkRT $ pure $ Value a
  (MkRT mf) <*> (MkRT ma) = MkRT $ do rf <- mf
                                      ra <- ma
                                      pure (rf <*> ra)

public export
Monad m => Monad (ResultT e m) where
  (MkRT ma) >>= f = MkRT $ ma >>= result (pure . HardFail) (pure . SoftFail) (runResultT . f)

public export
MonadTrans (ResultT e) where
  lift = MkRT . map Value
