module TParsec.Result

import public Control.Monad.Trans

%default total
%access public export

-- Result

data Result : Type -> Type -> Type where
  HardFail : e -> Result e a
  SoftFail : e -> Result e a
  Value : a -> Result e a

Functor (Result e) where
  map _ (SoftFail e) = SoftFail e
  map _ (HardFail e) = HardFail e
  map f (Value a)    = Value (f a)

Applicative (Result e) where
  pure = Value
  (HardFail e) <*> _ = HardFail e
  _ <*> (HardFail e) = HardFail e
  (SoftFail e) <*> _ = SoftFail e
  _ <*> (SoftFail e) = SoftFail e
  (Value f) <*> (Value a) = Value (f a)

Monad (Result e) where
  (HardFail e) >>= f = HardFail e
  (SoftFail e) >>= f = SoftFail e
  (Value a)    >>= f = f a

result : (h, s : e -> b) -> (v : a -> b) -> Result e a -> b
result h _ _ (HardFail e) = h e
result _ s _ (SoftFail e) = s e
result _ _ v (Value a)    = v a

fromMaybe : e -> Maybe a -> Result e a
fromMaybe e = maybe (SoftFail e) Value

record ResultT (e : Type) (m : Type -> Type) (a : Type) where
  constructor MkRT
  runResultT : m (Result e a)

Functor m => Functor (ResultT e m) where
  map f (MkRT fr) = MkRT $ map (map f) fr

Monad m => Applicative (ResultT e m) where
  pure a = MkRT $ pure $ Value a
  (MkRT mf) <*> (MkRT ma) = MkRT $ do rf <- mf
                                      ra <- ma
                                      pure (rf <*> ra)

Monad m => Monad (ResultT e m) where
  (MkRT ma) >>= f = MkRT $ ma >>= result (pure . HardFail) (pure . SoftFail) (runResultT . f)

MonadTrans (ResultT e) where
  lift = MkRT . map Value
