module Relation.Subset

import Util

%default total

public export
interface Subset (0 a : Type) (0 b : Type) where
  into : a -> b

public export
Subset Char String where
  into = singleton

public export
Subset a a where
  into = id
