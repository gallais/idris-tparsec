module TParsec.Position

%default total
%access public export

||| Position in the input string

record Position where
  constructor MkPosition
  ||| Line number (starting from 0)
  line   : Nat
  ||| Character offset in the given line
  offset : Nat

Show Position where
  show (MkPosition line offset) = show line ++ ":" ++ show offset

Eq Position where
  (MkPosition l1 o1) == (MkPosition l2 o2) = l1 == l2 && o1 == o2

start : Position
start = MkPosition 0 0

||| Every `Char` induces an action on `Position`s
update : Char -> Position -> Position
update c p = if c == '\n'
               then MkPosition (S (line p)) 0
               else record { offset = S (offset p) } p

updates : String -> Position -> Position
updates str p = foldl (flip update) p (unpack str)

next : Char -> Position -> Position
next = update 
%deprecate next "Please use `update` instead"
