module TParsec.Types

import Control.Monad.State
import TParsec.Success

%default total
%access public export

record Position where
  constructor MkPosition
  line : Nat
  offset : Nat
  
start : Position
start = MkPosition 0 0
  
next : Char -> Position -> Position
next c p = if c == '\n' 
           then MkPosition (S (line p)) 0 
           else record { offset = S (offset p) } p

-- A parser is parametrised by some types and type constructors.

record Parameters where
  constructor MkParameters
  Tok : Type          -- tokens
  Toks : Nat -> Type  -- sized input (~ Vec Tok)

-- Documentation-related parameters (cf. TParsec.Instruments):
  Pos  : Type         -- positions in the source file
  Ann  : Type         -- annotations tacked onto a subcomputation

  --Mn   : Type -> Type -- The monad stack used

posAnn : (tok : Type) -> (toks : Nat -> Type) -> (ann : Type) -> Parameters
posAnn tok toks ann = MkParameters tok toks Position ann --(StateT (Position, List ann) mn) 

unInstr : (tok : Type) -> (toks : Nat -> Type) -> Parameters
unInstr tok toks = MkParameters tok toks () Void --mn

-- A parser is the ability to, given an input, return a computation for
-- a success.

record Parser (p : Parameters)
           -- (toks : Nat -> Type) (tok : Type) 
              (mn : Type -> Type)
              (a : Type) (n : Nat) where
  constructor MkParser
  runParser : {m : Nat} -> LTE m n -> (Toks p) m -> mn (Success (Toks p) a m)  