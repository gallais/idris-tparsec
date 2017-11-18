module SizedDict

%default total
%access public export

data SizedDict : Type -> Type where
  MkSizedDict : Sized a => SizedDict a

sizeFromDict : SizedDict a -> a -> Nat
sizeFromDict MkSizedDict = size
