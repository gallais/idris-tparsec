module Relation.Subset

%default total
%access public export

interface Subset (a : Type) (b : Type) where
  into : a -> b
  
Subset Char String where
  into = singleton      

Subset a a where
  into = id
