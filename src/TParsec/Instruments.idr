module TParsec.Instruments

import Control.Monad.State
import TParsec.Types

%default total
%access public export

mapFst : (a -> c) -> (a, b) -> (c, b)
mapFst f (a, b) = (f a, b)

mapSnd : (b -> c) -> (a, b) -> (a, c)
mapSnd f (a, b) = (a, f b)

--------------------------------------------------------------------------------
-- An instrumented monad `M` for a parser parameterised by `P`

interface Instrumented (p : Parameters) (mn : Type -> Type) where
-- In `p` the two types we are most interested in are:
-- * Pos, the set of positions (in a file)
-- * Ann, the set of annotations

-- `withAnnotation ann m` puts the annotation `ann` on the subcomputation `m`.
-- Once `m` has finished the annotation should be discarded.
  withAnnotation : {a : Type} -> Ann p -> mn a -> mn a
-- `recordToken t` should be called every time a token `t` is read from the input
-- list of tokens. It should update the position stored in `M` accordingly.
  recordToken    : Tok p -> mn ()
-- We also provide the user with the ability to ask for:
-- * the current position in the file
-- * the current annotation
-- These capabilities can be used to put extra information in the AST produced
-- by the parser for precise error-reporting later on in the pipeline.
  getPosition    : mn (Pos p)
  getAnnotation  : mn (Maybe (Ann p))

--------------------------------------------------------------------------------
-- A typical implementation of Instruments for a character-based parser

Monad mn => Instrumented (posAnn Char chars an) (StateT (Position, List an) mn)  where
-- This instrumentation uses a state to keep track of:
-- * the current position in the file (given by a Position aka a `line` & an `offset`)
-- * the stack of annotations pushed onto the current subcomputation

-- `withAnnotation ann ma` pushes `ann` onto the stack, runs `ma` and then drops `ann`
-- We assume that `ma` leaves the stack as it found it!
  withAnnotation ann ma = do modify (mapSnd (List.(::) ann))
                             a <- ma
                             modify (mapSnd (List.drop 1))
                             pure a
  
-- `recordToken t` uses `Position`'s `next` to update the `line` & `offset`
  recordToken t = do modify (mapFst (next t))
                     pure ()

-- `getPosition` returns the current position
  getPosition = Basics.fst <$> get

-- `getAnnotation` returns the top of the stack (if it exists)
  getAnnotation = foldr (const . Just) Nothing . Basics.snd <$> get

--------------------------------------------------------------------------------
-- A non-instrumented version of Instruments

-- Straightforward definition ignoring the additional opportunities provided by
-- `Instruments`.

Monad mn => Instrumented (unInstr tok toks) mn where
  withAnnotation _ ma = ma
  recordToken _ = pure ()
  getPosition = pure ()
  getAnnotation = pure Nothing


