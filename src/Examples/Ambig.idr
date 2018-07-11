module Examples.Ambig 

import Control.Monad.State
import Data.NEList
import TParsec
import TParsec.Running

%default total

Params : Parameters
Params = posAnn Char (SizedList Char) Void 

PosM : Type -> Type
PosM = StateT Position (Either Position)

heuristic : Position -> Position -> Position
heuristic p1@(MkPosition r1 c1) p2@(MkPosition r2 c2) = 
  case compare r2 r1 of 
    LT => p1
    GT => p2
    EQ => if c1>c2 then p1 else p2

[altpos] Alternative PosM where
  empty = ST $ Left
  (ST a) <|> (ST b) = ST $ \pos => 
    case a pos of 
      Right x => Right x
      Left e1 => case b pos of
        Right x => Right x
        Left e2 => Left $ heuristic e1 e2

Parser' : Type -> Nat -> Type
Parser' = Parser Params PosM 

parse' : String -> All (Parser' a) -> Either Position a
parse' str p = let st = runParser p lteRefl $ MkSizedList $ tokenize str in 
               map (Success.Value . fst) $ runStateT st start

Instrumented Params PosM where
  withAnnotation Void _ impossible
  recordToken c = ST $ \pos => Right ((), next c pos)
  getPosition   = ST $ \pos => Right (pos, pos)
  getAnnotation = ST $ \pos => Right (Nothing, pos)

using implementation altpos  
  Amb : All (Parser' String)
  Amb = string "abracadabra" `alt` string "abraham"

test : parse' "abracadazra" Amb = Left (MkPosition 0 9)  
test = Refl
