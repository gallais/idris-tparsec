module Examples.Lexing

import TParsec.Lexer

%default total
%access public export

-- A small set of keywords for a language with expressions of the form
-- `let x = e in b`.

data TOK = LET | EQ | IN | LPAR | RPAR | ID String

toks : List (String, TOK)
toks = [ ("let", LET)
       , ("="  , EQ)
       , ("in" , IN)
       ]

-- Breaking characters: spaces (thrown away) and parentheses (kept)

breaking : Char -> MaybeBreaking TOK
breaking c = if isSpace c then Breaking Nothing else parens c where
  parens : Char -> MaybeBreaking TOK
  parens '(' = Breaking (Just LPAR)
  parens ')' = Breaking (Just RPAR)
  parens _   = NotBreaking

Params : LexParameters
Params = MkLexParameters TOK toks breaking ID

TestTy : Type
TestTy = tokenize {p=Params} "fix f x = let b = fix f in (f b) x" =
           [ (MkPosition 0 0 , ID "fix")
           , (MkPosition 0 4 , ID "f")
           , (MkPosition 0 6 , ID "x")
           , (MkPosition 0 8 , EQ)
           , (MkPosition 0 10, LET)
           , (MkPosition 0 14, ID "b")
           , (MkPosition 0 16, EQ)
           , (MkPosition 0 18, ID "fix")
           , (MkPosition 0 22, ID "f")
           , (MkPosition 0 24, IN)
           , (MkPosition 0 27, LPAR)
           , (MkPosition 0 28, ID "f")
           , (MkPosition 0 30, ID "b")
           , (MkPosition 0 31, RPAR)
           , (MkPosition 0 33, ID "x")
           ]

test : TestTy
test = Refl
