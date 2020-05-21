module TParsec.Combinators

import Relation.Indexed
import Induction.Nat as Box
import Data.Inspect
import Data.NEList
import Data.Vect
import TParsec.Success
import TParsec.Types

%default total
%access public export

lteLower : LTE m n -> Parser mn p a n -> Parser mn p a m
lteLower mlen p = MkParser (\plem => runParser p (lteTransitive plem mlen))

ltLower : LT m n -> Parser mn p a n -> Parser mn p a m
ltLower mltn = lteLower (lteSuccLeft mltn)

implicit
box : Parser mn p a n -> Box (Parser mn p a) n
box = lteClose lteLower

lift2 : All (Parser mn p a :-> Parser mn p b :-> Parser mn p c) ->
        All (Box (Parser mn p a) :-> Box (Parser mn p b) :-> Box (Parser mn p c))
lift2 = map2

lift2l : All (Parser mn p a :-> Parser mn p b :-> Parser mn p c) ->
         All (Box (Parser mn p a) :-> Parser mn p b :-> Box (Parser mn p c))
lift2l f a b = lift2 f a (box b)

lift2r : All (Parser mn p a :-> Parser mn p b :-> Parser mn p c) ->
         All (Parser mn p a :-> Box (Parser mn p b) :-> Box (Parser mn p c))
lift2r f a b = lift2 f (box a) b

||| Parses any token.
|||
||| Assuming the token we are trying to parse consumes a non-empty prefix
||| of the input, this will always succeed and return the parsed
||| token.
|||
||| Unindexed signature: `Parser a`
anyTok : (Alternative mn, Inspect (Toks p) (Tok p)) =>
         All (Parser mn p (Tok p))
anyTok {p} = MkParser $ \_, ts =>
  choiceMap (\t => recordToken p (Value t) *> pure t)
            (getTok {toks=Toks p} {tok=Tok p} ts)

guardM : (Alternative mn, Monad mn) =>
         (a -> Maybe b) -> All (Parser mn p a :-> Parser mn p b)
guardM f p = MkParser $ \mlen, ts => do s <- runParser p mlen ts
                                        choiceMap pure (Success.guardM f s)

||| Constrains a parser to succeed only when a predicate holds.
|||
||| Given a predicate on a value, and a parser of such value,
||| this will fail when the predicate is false and will return the value if
||| the predicate is true.
|||
||| Unindexed signature: `(a -> Bool) -> Parser a -> Parser a`
guard : (Alternative mn, Monad mn) =>
        (a -> Bool) -> All (Parser mn p a :-> Parser mn p a)
guard p = guardM $ \v => toMaybe (p v) v

||| Processes a token into a `Maybe` value.
|||
||| Given a function that maps a parsed token into a `Maybe a`, this function
||| will fail when the token is mapped to `Nothing` and
||| succeeds when the value is mapped into a `Just` value. The successful
||| value is then unwrapped and `Parser a` is returned.
|||
||| Unindexed signature: `(Tok p -> Maybe a) -> Parser a`
maybeTok : (Alternative mn, Monad mn, Inspect (Toks p) (Tok p)) =>
           (Tok p -> Maybe a) -> All (Parser mn p a)
maybeTok p = guardM p anyTok

||| Given a function (a -> b), transforms a `Parser a` into a `Parser b`.
|||
||| Map lifts a function from `a -> b` to `Parser a -> Parser b`. This
||| function signature does not follow the traditional `Functor` signature
||| (which is `(a -> b) -> F a -> F b`) due to the indexing rules that ensure
||| totality.
|||
||| Unindexed signature: `(a -> b) -> Parser a -> Parser b`
map : Functor mn =>
      (a -> b) -> All (Parser mn p a :-> Parser mn p b)
map f p = MkParser $ \le, ts => Functor.map (Success.map f) (runParser p le ts)

||| Assuming the parser is successful, returns the given value.
|||
||| Given a value `v` of type `a` this function will replace the parsed value
||| by `v`, assuming it is successful. The parsed value is discarded.
|||
||| Unindexed signature: `b -> Parser a -> Parser b`
cmap : Functor mn => b -> All (Parser mn p a :-> Parser mn p b)
cmap b = map (\_ => b)

||| A parser that always fail.
|||
||| Unindexed signature: `Parser a`
fail : Alternative mn => All (Parser mn p a)
fail = MkParser $ \_, _ => empty

||| Given two parser, takes the first one that succeeds.
|||
||| If the first parser fails, the second one will be attempted, if the second
||| one fails the whole parser fails. This is analogous to an `or` operation.
|||
||| Unindexed signature: `Parser a -> Parser a -> Parser a`
alt : Alternative mn =>
      All (Parser mn p a :-> Parser mn p a :->
           Parser mn p a)
alt p q = MkParser $ \mlen, ts => runParser p mlen ts <|> runParser q mlen ts

||| Given a list of parsers, takes the first one that succeeds, in order.
|||
||| Attempt parsing using each parser in the list. If all fail, then this
||| parser will fail too. If one succeeds, then the following parsers will
||| not be attempted and the parser will succeed.
|||
||| Unindexed signature: `List (Parser a) -> Parser a`
alts : Alternative mn =>
       All (List :. Parser mn p a :-> Parser mn p a)
alts = foldr alt fail

||| Parses a value and processes it into another parser.
|||
||| Given a `Parser a` and a function `a -> Parser b` this function will
||| attempt the first parser on the input and run the function on the
||| parsed value. Both values are returned as a pair. As long as the first
||| parser is successful this parser will be successful. If the second parser
||| fails and the first one succeeds, this will return `Nothing` as the second
||| element of the pair.
|||
||| Unindexed signature: `Parser a -> (a -> Parser b) -> Parser (a, Maybe b)`
andoptbind : (Monad mn, Alternative mn) =>
             All (Parser mn p a :-> (Cst a :-> Box (Parser mn p b)) :->
                  Parser mn p (a, Maybe b))
andoptbind p q = MkParser $ \mlen, ts =>
                 do sa <- runParser p mlen ts
                    let salen   = lteTransitive (Small sa) mlen
                    let combine = Success.map (Functor.map Just) . (Success.and sa)
                    (Functor.map combine (runParser (call (q (Value sa)) salen) lteRefl (Leftovers sa))) <|> pure (Success.map (flip MkPair Nothing) sa)

||| Parses a value and processes it into another parser.
|||
||| Given a `Parser a` and a function `a -> Parser b` this function will
||| attempt the first parser on the input, and run the function on the
||| parsed value. If both those steps are successful, both values are
||| returned as a pair.
|||
||| Unindexed signature: `Parser a -> (a -> Parser b) -> Parser (a, b)`
andbind : Monad mn =>
          All (Parser mn p a :-> (Cst a :-> Box (Parser mn p b)) :->
               Parser mn p (a, b))
andbind p q = MkParser $ \mlen, ts =>
                do sa <- runParser p mlen ts
                   let salen  = lteTransitive (Small sa) mlen
                   let adjust = Functor.map (Success.and sa)
                   adjust (runParser (call (q (Value sa)) salen) lteRefl (Leftovers sa))

||| Parses a values and processes it in the context of a monad.
|||
||| Given a Monad `M`, a parser `Parser M a` that executes in this monad,
||| and a function `a -> M b` this function will attempt the parser
||| on the input, and run the function on the parsed value. If the parser
||| is successful both values are returned as a pair.
|||
||| Unindexed signature: `Parser M a -> (a -> M b) -> Parser M (a, b)`
andbindm : Monad mn =>
  All (Parser mn p a :-> Cst (a -> mn b) :-> Parser mn p (a, b))
andbindm p f = MkParser $ \mlen, ts => do ra <- runParser p mlen ts
                                          b <- f (Value ra)
                                          pure $ map (flip MkPair b) ra

||| Like `andbindm` but ignores the second argument's output.
|||
||| This function takes a parser and a function that processes the
||| output of the first parser in a monad `M`. This function only
||| returns the value of the first parser and not the result of the
||| computation.
|||
||| Unindexed signature: `Parser M a -> (a -> M b) -> Parser M a`
landbindm : Monad mn =>
  All (Parser mn p a :-> Cst (a -> mn b) :-> Parser mn p a)
landbindm p f = map fst (andbindm p f)

||| Like `andbindm` but ignores the parser's output.
|||
||| This function takes a parser and a function that processes the
||| output of the first parser in a monad `M`. This function only
||| returns the value of the computation and ignore the output of
||| the parser.
|||
||| Unindexed signature: `Parser M a -> (a -> M b) -> Parser M b)`
randbindm : Monad mn =>
  All (Parser mn p a :-> Cst (a -> mn b) :-> Parser mn p b)
randbindm p f = map snd (andbindm p f)

||| Runs two parsers in succession.
|||
||| Run two parsers one after the other. If any of the two parsers
||| fail this fails. The result of both parsers is returned as
||| a pair. This is analogous to an `and` operation.
|||
||| Unindexed signature: `Parser a -> Parser b -> Parser (a, b)`
and : Monad mn =>
      All (Parser mn p a :-> Box (Parser mn p b) :-> Parser mn p (a, b))
and p q = andbind p (\ _ => q)

||| Runs the same parser n times.
|||
||| The number n needs to be non-zero. Otherwise the parser simply fails.
|||
||| Unindexed signature: `(n : Nat) -> Parser a -> Parser (Vect n a)`
replicate : (Monad mn, Alternative mn) =>
            (n : Nat) -> All (Parser mn p a :-> Parser mn p (Vect n a))
replicate Z     p = Combinators.fail
replicate (S Z) p = map (:: []) p
replicate (S n) p = map (uncurry (::)) $ and p (box $ replicate n p)

||| Runs a list of parsers in succession.
|||
||| Runs a list of parser one after the other. All parsers must
||| succeed for this to succeed. The result of each parser is
||| returned as a list. The list of parser is non-empty and
||| the list of results is non-empty as well.
|||
||| Unindexed signature: `NEList (Parser a) -> Parser (NEList a)`
ands : Monad mn =>
       All (NEList :. Parser mn p a :-> Parser mn p (NEList a))
ands ps = NEList.foldr1 (\ p, ps => map (uncurry (<+>)) (and p ps))
                        (Functor.map (map singleton) ps)

||| Runs a parser and a monadic computation in succession.
|||
||| Given a monad `M`, a parser `Parser M a` and a value `M b` this
||| function will run the parser first and then run the monadic
||| computation `M b`. Both results are returned as a pair.
|||
||| Unindexed signature: `Parser M a -> M b -> Parser M (a, b)`
andm : Monad mn =>
       All (Parser mn p a :-> Cst (mn b) :-> Parser mn p (a, b))
andm p q = MkParser $ \mlen, ts => do ra <- runParser p mlen ts
                                      b <- q
                                      pure $ map (flip MkPair b) ra

||| Runs a parser and a monadic computation but discards the computation's result
|||
||| Given a monad `M`, a parser `Parser M a` and a computation `M b`
||| this function will run the parser first and then run the monadic
||| computation `M b`. The result of the monadic computation is
||| discarded.
|||
||| Unindexed signature: `Parser M a -> M b -> Parser M a`
landm : Monad mn =>
        All (Parser mn p a :-> Cst (mn b) :-> Parser mn p a)
landm p q = map fst (andm p q)

||| Runs a parser and a monadic computation but discard the parser's result
|||
||| Given a monad `M`, a parser `Parser M a` and a computation `M b`
||| this function will run the parser first and then run the monadic
||| computation `M b`. The result of the parser is discarded.
|||
||| Unindexed signature: `Parser M a -> M b -> Parser M b`
randm : Monad mn =>
        All (Parser mn p a :-> Cst (mn b) :-> Parser mn p b)
randm p q = map snd (andm p q)

||| Runs a monadic computation and a parser in succession.
|||
||| Given a monad `M`, a monadic computation `M a` and a parser `Parser M a`
||| this function will run the computation `M a` first and then run the
||| parser. Both results are returned as a pair.
|||
||| Unindexed signature: `M a -> Parser M b -> Parser M (a, b)`
mand : Monad mn =>
       All (Cst (mn a) :-> Parser mn p b :-> Parser mn p (a, b))
mand p q = MkParser $ \mlen, ts => do a <- p
                                      Functor.map (Success.map (MkPair a)) (runParser q mlen ts)

||| Runs a monadic computation and a parser but discards the parser's result.
|||
||| Given a monad `M`, a monadic computation `M a` and a parser `Parser M a`
||| this function will run the computation `M a` first and then run the
||| parser. The result of the parser is discarded.
|||
||| Unindexed signature: `M a -> Parser M b -> Parser M a`
lmand : Monad mn =>
        All (Cst (mn a) :-> Parser mn p b :-> Parser mn p a)
lmand p q = map fst (mand p q)

||| Runs a monadic computation and parser but discards the computation's result.
|||
||| Given a monad `M`, a monadic computation `M a` and a parser `Parser M a`
||| this function will run the computation `M a` first and then run the
||| parser. The result of the computation is discarded.
|||
||| Unindexed signature: `M a -> Parser M b -> Parser M b`
rmand : Monad mn =>
        All (Cst (mn a) :-> Parser mn p b :-> Parser mn p b)
rmand p q = map snd (mand p q)

||| Runs two parsers in succession but the second one is allowed to fail.
|||
||| Runs two parsers one after the other, this parser succeeds as long
||| as the first parser succeeds. If the second one fails, its value
||| will be reported as `Nothing`. Both values are returned as a pair.
|||
||| Unindexed signature: `Parser a -> Parser b -> Parser (a, Maybe b)`
andopt : (Monad mn, Alternative mn) =>
         All (Parser mn p a :-> Box (Parser mn p b) :-> Parser mn p (a, Maybe b))
andopt p q = andoptbind p (\ _ => q)

||| Runs two parsers in succession but the first one is allowed to fail.
|||
||| Runs two parsers one after the other, this parser succeeds as long
||| as the second parser succeeds. If the first one fails, its value
||| will be reported as `Nothing`. Both values are returned as a pair.
|||
||| Unindexed signature: `Parser a -> Parser b -> Parser (Maybe a, b)`
optand : (Monad mn, Alternative mn) =>
         All (Parser mn p a :-> Parser mn p b :-> Parser mn p (Maybe a, b))
optand p q = alt (and (map Just p) q) (map (MkPair Nothing) q)

||| Parses a value and processes it into another parser.
|||
||| Given a `Parser a` and a function `a -> Parser b` this function will
||| attempt the first parser on the input, and run the function on the
||| parsed value. The result of the first parser is discarded.
|||
||| Unindexed signature: `Parser a -> (a -> Parser b) -> Parser b`
bind : Monad mn =>
       All (Parser mn p a :-> (Cst a :-> Box (Parser mn p b)) :-> Parser mn p b)
bind p q = map snd (andbind p q)

||| Runs two parsers in succession but discards the second value.
|||
||| Runs two parsers one after the other, this parser succeeds if
||| both parsers succeed. The parsed value of the second one is
||| discarded.
|||
||| Unindexed signature: `Parser a -> Parser b -> Parser a`
land : (Monad mn, Alternative mn) =>
       All (Parser mn p a :-> Box (Parser mn p b) :-> Parser mn p a)
land p q = map fst (and p q)

||| Runs two parsers in succession but discards the first value.
|||
||| Runs two parsers one after the other, this parser succeeds if
||| both parsers succeed. The parsed value of the first one is
||| discarded.
|||
||| Unindexed signature: `Parser a -> Parser b -> Parser b`
rand : (Monad mn, Alternative mn) =>
       All (Parser mn p a :-> Box (Parser mn p b) :-> Parser mn p b)
rand p q = map snd (and p q)

||| Runs two parsers in succession, discards the second value, second parser might fail.
|||
||| Runs two parsers one after the other, this parser suceeds as
||| long as the first parser succeeds, the second one might fail.
||| The value parsed by the second parser is discarded and only
||| the value parsed by the first is returned.
|||
||| Unindexed signature: `Parser a -> Parser b -> Parser a`
landopt : (Monad mn, Alternative mn) =>
          All (Parser mn p a :-> Box (Parser mn p b) :-> Parser mn p a)
landopt p q = map fst (andopt p q)

||| Runs two parsers in succession, discards the first value, second parser might fail.
|||
||| Runs two parsers one after the other, this parser suceeds as
||| long as the first parser succeeds. The value parsed by the first
||| parser is discarded. If the second parser fails the value
||| `Nothing` is returned.
|||
||| Unindexed signature: `Parser a -> Parser b -> Parser (Maybe b)`
randopt : (Monad mn, Alternative mn) =>
          All (Parser mn p a :-> Box (Parser mn p b) :-> Parser mn p (Maybe b))
randopt p q = map snd (andopt p q)

||| Runs two parsers in succession, discards the second value, first parser might fail.
|||
||| Runs two parsers one after the other, this parser suceeds as
||| long as the second parser succeeds. The value parsed by the second
||| parser is discarded. If the first parser fails the value
||| `Nothing` is returned.
|||
||| Unindexed signature: `Parser a -> Parser b -> Parser (Maybe a)`
loptand : (Monad mn, Alternative mn) =>
          All (Parser mn p a :-> Parser mn p b :-> Parser mn p (Maybe a))
loptand p q = map fst (optand p q)


||| Runs two parsers in succession, discards the first value, first parser might fail.
|||
||| Runs two parsers one after the other, this parser suceeds as
||| long as the second parser succeeds, the first one might fail.
||| The value parsed by the first parser is discarded and only
||| the value parsed by the second is returned.
|||
||| Unindexed signature: `Parser a -> Parser b -> Parser b`
roptand : (Monad mn, Alternative mn) =>
          All (Parser mn p a :-> Parser mn p b :-> Parser mn p b)
roptand p q = map snd (optand p q)

||| Given two different parsers, returns the first successfully parsed value.
|||
||| Given two parsers `Parser a` and `Parser b`, this will run the first
||| parser and wrap the result in a `Left` if it is successful. Otherwise,
||| it will run the second parser and wrap the result in a `Right` if it is
||| successful.
|||
||| Unindexed signature: `Parser a -> Parser b -> Parser (Either a b)`
sum : Alternative mn =>
      All (Parser mn p a :-> Parser mn p b :-> Parser mn p (Either a b))
sum p q = alt (map Left p) (map Right q)

||| Applies a parsed value to a parsed function.
|||
||| Given a parsed function `Parser (a -> b)` and a parsed value `Parser a`
||| this will apply the value to the function and return it as a parsed
||| value `Parser b`.
|||
||| Unindexed signature: `Parser (a -> b) -> Parser a -> Parser b`
app : Monad mn =>
      All (Parser mn p (a -> b) :-> Box (Parser mn p a) :-> Parser mn p b)
app p q = bind p (\ f => Box.map (map f) q)

||| Parses the given token.
|||
||| Given a token `p`, return a parser that will only succeed if it encounters
||| this token and will fail otherwise.
|||
||| Unindexed signature: `p -> Parser p`
exact : (Alternative mn, Monad mn, Inspect (Toks p) (Tok p), Eq (Tok p)) =>
        Tok p -> All (Parser mn p (Tok p))
exact t = guard (\t' => t == t') anyTok

||| Given a list of tokens, parses them all in order.
|||
||| Given a list of tokens to be parsed in the given order, return a parser
||| that will expect this series of token exactly and return the result
||| as a list of values. The list of tokens has to be non-empty.
|||
||| Unindexed signature: `List p -> Parser (List p)`
exacts : (Alternative mn, Monad mn, Inspect (Toks p) (Tok p), Eq (Tok p)) =>
         NEList (Tok p) -> All (Parser mn p (NEList (Tok p)))
exacts ts = ands (map (\t => exact t) ts)

||| Given a token, always succeeds unless it is encountered.
|||
||| Given a rejected token, this parser will always succeed as long as the
||| rejected token is not met in the input.
|||
||| Unindexed signature: `p -> Parser p`
anyTokenBut : (Alternative mn, Monad mn, Inspect (Toks p) (Tok p), Eq (Tok p)) =>
              Tok p -> All (Parser mn p (Tok p))
anyTokenBut t = guard (\t' => (t /= t')) anyTok

||| Given a list of token, fails if the input starts with one of them.
|||
||| Given a list of rejected tokens, return a parser that will succeed only
||| if it does not encounter one of the tokens in the input. Conversely, it
||| will fail if the input begins with one of the rejected tokens.
|||
||| Unindexed signature: `List p -> Parser p`
noneOf : (Alternative mn, Monad mn, Inspect (Toks p) (Tok p), Eq (Tok p)) =>
         List (Tok p) -> All (Parser mn p (Tok p))
noneOf ts = guard (\t' => all (/= t') ts) anyTok

||| Given a list of token, succeeds if the input starts with one of them.
|||
||| Given a list of acceptable tokens, return a parser that will succeed only
||| if it encounters one of the tokens in the input.
|||
||| Unindexed signature: `List p -> Parser p`
anyOf : (Alternative mn, Monad mn, Inspect (Toks p) (Tok p), Eq (Tok p)) =>
        List (Tok p) -> All (Parser mn p (Tok p))
anyOf ts = alts (map (\t => exact t) ts)

||| Parses anything between two other parsers.
|||
||| Given an _opening_ parser, a _closing_ parser and a _middle_ parser this
||| parser will succeed as long as _opening_, _middle_ and _closing_ parser
||| all succeed when executed in that order. Only the _middle_ parser will
||| return its value.
|||
||| Unindexed signature: `Parser a -> Parser c -> Parser b -> Parser b`
between : (Monad mn, Alternative mn) =>
          All (Parser mn p a :-> Box (Parser mn p c) :->
          Box (Parser mn p b) :-> Parser mn p b)
between open close p = land (rand open p) close

||| Parses anything that might be between two other parsers.
|||
||| Given an _opening_ parser, a _closing_ parser and a _middle_ parser this
||| parser will succeed as long as _opening_, _middle_ and _closing_ parser
||| all succeed when executed in that order. Or if the surrounding parsers
||| fail. Only the _middle_ parser will return its value.
|||
||| Unindexed signature: `Parser a -> Parser c -> Parser b -> Parser b`
betweenopt : (Monad mn, Alternative mn) =>
             All (Parser mn p a :-> Box (Parser mn p c) :->
             Parser mn p b :-> Parser mn p b)
betweenopt open close p = between open close p `alt` p

LChain : Parameters mn -> Type -> Nat -> Type
LChain p {mn} a n =
  Success (Toks p) a n -> Box (Parser mn p (a -> a)) n -> mn (Success (Toks p) a n)

schainl : (Alternative mn, Monad mn) => All (LChain {mn} p a)
schainl {mn} {a} {p} = fix _ $ \rec, sa, op => schainlAux rec sa op <|> pure sa
  where
  schainlAux : All (Box (LChain {mn} p a) :-> LChain {mn} p a)
  schainlAux rec sa op = do sop <- runParser (call op (Small sa)) lteRefl (Leftovers sa)
                            let sa' = Success.map (\f => f (Value sa)) sop
                            res <- call rec (Small sa) sa' (Box.ltLower (Small sa) op)
                            pure (ltLift (Small sa) res)

iteratel : (Alternative mn, Monad mn) =>
           All (Parser mn p a :-> Box (Parser mn p (a -> a)) :-> Parser mn p a)
iteratel val op = MkParser $ \mlen, ts => do sa <- runParser val mlen ts
                                             schainl sa (Box.lteLower mlen op)

RChain : Parameters mn -> Type -> Nat -> Type
RChain p {mn} a n =
  Parser mn p (a -> a) n -> Parser mn p a n -> Parser mn p a n

iterater : (Alternative mn, Monad mn) =>
           All (Parser mn p (a -> a) :-> Parser mn p a :-> Parser mn p a)
iterater {mn} {p} {a} = fix (RChain p a) $ \rec, op, val =>
                                     alt (iteraterAux rec op val) val
  where
  iteraterAux : All (Box (RChain p a) :-> RChain p a)
  iteraterAux rec op val = MkParser $ \mlen, ts =>
    do sop <- runParser op mlen ts
       let sopltn = lteTransitive (Small sop) mlen
       let op'    = ltLower sopltn op
       let val'   = ltLower sopltn val
       res <- runParser (call rec sopltn op' val') lteRefl (Leftovers sop)
       pure (ltLift (Small sop) (Success.map (Value sop) res))

hchainl : (Alternative mn, Monad mn) =>
          All (Parser mn p a :-> Box (Parser mn p (a -> b -> a)) :->
          Box (Parser mn p b) :-> Parser mn p a)
hchainl {p} {mn} {a} {b} seed op arg =
  let ty   = Parser mn p
      op'  = Box.map {a = ty (a -> b -> a)} (map flip) op
      arg' = duplicate arg
     in
  iteratel seed (map2 {a = ty (b -> a -> a)} app op' arg')

hchainr : (Alternative mn, Monad mn) =>
          All (Parser mn p a :-> Box (Parser mn p (a -> b -> b)) :->
               Parser mn p b :-> Parser mn p b)
hchainr arg op seed = iterater (app (map (flip apply) arg) op) seed

chainl1 : (Alternative mn, Monad mn) =>
          All (Parser mn p a :-> Box (Parser mn p (a -> a -> a)) :->
          Parser mn p a)
chainl1 p op = hchainl p op p

chainr1 : (Alternative mn, Monad mn) =>
          All (Parser mn p a :-> Box (Parser mn p (a -> a -> a)) :->
          Parser mn p a)
chainr1 p op = hchainr p op p

||| Given a parser, parses a non-empty list of it.
|||
||| This will parse a list whose elements are accepted by the
||| parser in argument. The list has to be non-empty, otherwise
||| the parser will fail. The list has no separator.
|||
||| Unindexed signature: `Parser a -> Parser (List a)`
nelist : (Alternative mn, Monad mn) =>
         All (Parser mn p a :-> Parser mn p (NEList a))
nelist = fix _ $ \rec, p => Combinators.map (uncurry consopt) (andopt p (Box.app rec p))
