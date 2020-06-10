module TParsec.Position

%default total

||| Position in the input string
public export
record Position where
  constructor MkPosition
  ||| Line number (starting from 0)
  line   : Nat
  ||| Character offset in the given line
  offset : Nat

public export
Show Position where
  show (MkPosition line offset) = show line ++ ":" ++ show offset

public export
Eq Position where
  (MkPosition l1 o1) == (MkPosition l2 o2) = l1 == l2 && o1 == o2

public export
start : Position
start = MkPosition 0 0

||| Every `Char` induces an action on `Position`s
public export
update : Char -> Position -> Position
update c p = if c == '\n'
               then MkPosition (S (line p)) 0
               else record { offset = S (offset p) } p

public export
updates : String -> Position -> Position
updates str p = foldl (flip update) p (unpack str)
