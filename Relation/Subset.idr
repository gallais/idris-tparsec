module Relation.Subset

import Util

public export
interface Subset (a : Type) (b : Type) where
  into : a -> b

export
Subset Char String where
  into = singleton

export
Subset a a where
  into = id
