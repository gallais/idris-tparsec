module TParsec.Combinators

import TParsec.Indexed
import TParsec.Induction as Box
import TParsec.Inspect
import TParsec.Success
import TParsec.NEList

%default total
%access public export

record Parser (toks : Nat -> Type) (tok : Type)
              (mn : Type -> Type) (a : Type) (n : Nat) where
  constructor MkParser
  runParser : {m : Nat} -> LTE m n -> toks m -> mn (Success toks tok a m)

lteLower : LTE m n -> Parser toks tok mn a n -> Parser toks tok mn a m
lteLower mlen p = MkParser (\ plem => runParser p (lteTransitive plem mlen))

ltLower : LT m n -> Parser toks tok mn a n -> Parser toks tok mn a m
ltLower mltn = lteLower (lteSuccLeft mltn)

implicit box : Parser toks tok mn a n -> Box (Parser toks tok mn a) n
box = lteClose lteLower

anyTok : (Inspect toks tok, Alternative mn) =>
         All (Parser toks tok mn tok)
anyTok = MkParser (\ mlen, ts => choiceMap pure (getTok ts))

guardM : (Alternative mn, Monad mn) =>
         (a -> Maybe b) -> All (Parser toks tok mn a :-> Parser toks tok mn b)
guardM f p = MkParser (\ mlen, ts => runParser p mlen ts >>= \ s =>
                       choiceMap pure (Success.guardM f s))

guard : (Alternative mn, Monad mn) =>
        (a -> Bool) -> All (Parser toks tok mn a :-> Parser toks tok mn a)
guard p = guardM (\ v => if p v then Just v else Nothing)

maybeTok : (Inspect toks tok, Alternative mn, Monad mn) =>
           (tok -> Maybe a) -> All (Parser toks tok mn a)
maybeTok p = guardM p anyTok

map : Functor mn =>
      (a -> b) -> All (Parser toks tok mn a :-> Parser toks tok mn b)
map f p = MkParser (\ le, ts => Functor.map (Success.map f) (runParser p le ts))

cmap : Functor mn => b -> All (Parser toks tok mn a :-> Parser toks tok mn b)
cmap b = map (\ _ => b)

fail : Alternative mn => All (Parser toks tok mn a)
fail = MkParser (\ _, _ => empty)

alt : Alternative mn =>
      All (Parser toks tok mn a :-> Parser toks tok mn a :->
           Parser toks tok mn a)
alt p q = MkParser (\ mlen, ts => runParser p mlen ts <|> runParser q mlen ts)

alts : Alternative mn =>
       All (List :. Parser toks tok mn a :-> Parser toks tok mn a)
alts = foldr alt fail

andmbind : (Monad mn, Alternative mn) =>
           All (Parser toks tok mn a :-> (Cst a :-> Box (Parser toks tok mn b)) :->
                Parser toks tok mn (a, Maybe b))
andmbind p q = MkParser (\ mlen, ts =>
               runParser p mlen ts >>= \ sa =>
               let salen   = lteTransitive (Small sa) mlen in
               let combine = Success.map (Functor.map Just) . (Success.and sa) in
               (Functor.map combine (runParser (call (q (Value sa)) salen) lteRefl (Leftovers sa)))
               <|> pure (Success.map (flip MkPair Nothing) sa))

andbind : Monad mn =>
           All (Parser toks tok mn a :-> (Cst a :-> Box (Parser toks tok mn b)) :->
                Parser toks tok mn (a, b))
andbind p q = MkParser (\ mlen, ts =>
              runParser p mlen ts >>= \ sa =>
              let salen  = lteTransitive (Small sa) mlen in
              let adjust = Functor.map (Success.and sa) in
              adjust (runParser (call (q (Value sa)) salen) lteRefl (Leftovers sa)))

and : Monad mn =>
      All (Parser toks tok mn a :-> Box (Parser toks tok mn b) :-> Parser toks tok mn (a, b))
and p q = andbind p (\ _ => q)

ands : Monad mn =>
       All (NEList :. Parser toks tok mn a :-> Parser toks tok mn (NEList a))
ands ps = foldr1 (\ p, ps => map (uncurry (<+>)) (and p ps)) (Functor.map (map singleton) ps)

andm : (Monad mn, Alternative mn) =>
       All (Parser toks tok mn a :-> Box (Parser toks tok mn b) :->
       Parser toks tok mn (a, Maybe b))
andm p q = andmbind p (\ _ => q)

mand : (Monad mn, Alternative mn) =>
       All (Parser toks tok mn a :-> Parser toks tok mn b :-> Parser toks tok mn (Maybe a, b))
mand p q = alt (and (map Just p) q) (map (MkPair Nothing) q)

bind : Monad mn =>
       All (Parser toks tok mn a :-> (Cst a :-> Box (Parser toks tok mn b)) :-> Parser toks tok mn b)
bind p q = map snd (andbind p q)

land : (Monad mn, Alternative mn) =>
       All (Parser toks tok mn a :-> Box (Parser toks tok mn b) :-> Parser toks tok mn a)
land p q = map fst (and p q)

rand : (Monad mn, Alternative mn) =>
       All (Parser toks tok mn a :-> Box (Parser toks tok mn b) :-> Parser toks tok mn b)
rand p q = map snd (and p q)

landm : (Monad mn, Alternative mn) =>
        All (Parser toks tok mn a :-> Box (Parser toks tok mn b) :-> Parser toks tok mn a)
landm p q = map fst (andm p q)

randm : (Monad mn, Alternative mn) =>
        All (Parser toks tok mn a :-> Box (Parser toks tok mn b) :-> Parser toks tok mn (Maybe b))
randm p q = map snd (andm p q)

lmand : (Monad mn, Alternative mn) =>
        All (Parser toks tok mn a :-> Parser toks tok mn b :-> Parser toks tok mn (Maybe a))
lmand p q = map fst (mand p q)

rmand : (Monad mn, Alternative mn) =>
        All (Parser toks tok mn a :-> Parser toks tok mn b :-> Parser toks tok mn b)
rmand p q = map snd (mand p q)

sum : (Alternative mn) =>
      All (Parser toks tok mn a :-> Parser toks tok mn b :-> Parser toks tok mn (Either a b))
sum p q = alt (map Left p) (map Right q)

app : Monad mn =>
      All (Parser toks tok mn (a -> b) :-> Box (Parser toks tok mn a) :-> Parser toks tok mn b)
app p q = bind p (\ f => Box.map (map f) q)

exact : (Inspect toks tok, DecEq tok, Monad mn, Alternative mn) =>
        tok -> All (Parser toks tok mn tok)
exact t = guard (\ t' => decAsBool (decEq t t')) anyTok

exacts : (Inspect toks tok, DecEq tok, Monad mn, Alternative mn) =>
         NEList tok -> All (Parser toks tok mn (NEList tok))
exacts ts = ands (map (\ t => exact t) ts)

anyOf : (Inspect toks tok, DecEq tok, Monad mn, Alternative mn) =>
        List tok -> All (Parser toks tok mn tok)
anyOf ts = alts (map (\ t => exact t) ts)

between : (Monad mn, Alternative mn) =>
          All (Parser toks tok mn a :-> Box (Parser toks tok mn c) :->
          Box (Parser toks tok mn b) :-> Parser toks tok mn b)
between open close p = land (rand open p) close

betweenm : (Monad mn, Alternative mn) =>
           All (Parser toks tok mn a :-> Box (Parser toks tok mn c) :->
           Parser toks tok mn b :-> Parser toks tok mn b)
betweenm open close p = landm (rmand open p) close

LChain : (Nat -> Type) -> Type -> (Type -> Type) -> Type -> Nat -> Type
LChain toks tok mn a n =
  Success toks tok a n -> Box (Parser toks tok mn (a -> a)) n -> mn (Success toks tok a n)

schainl : (Alternative mn, Monad mn) => All (LChain toks tok mn a)
schainl {mn} {a} = fix _ $ \ rec, sa, op => schainlAux rec sa op <|> pure sa where

  schainlAux : All (Box (LChain toks tok mn a) :-> LChain toks tok mn a)
  schainlAux rec sa op =
    runParser (call op (Small sa)) lteRefl (Leftovers sa) >>= \ sop =>
    let sa' = Success.map (\ f => f (Value sa)) sop in
    call rec (Small sa) sa' (Box.ltLower (Small sa) op) >>= \ res =>
    pure (ltLift (Small sa) res)

iteratel : (Alternative mn, Monad mn) =>
           All (Parser toks tok mn a :-> Box (Parser toks tok mn (a -> a)) :-> Parser toks tok mn a)
iteratel val op = MkParser (\ mlen, ts => runParser val mlen ts >>=
                            \ sa => schainl sa (Box.lteLower mlen op))

RChain : (Nat -> Type) -> Type -> (Type -> Type) -> Type -> Nat -> Type
RChain toks tok mn a n =
  Parser toks tok mn (a -> a) n -> Parser toks tok mn a n -> Parser toks tok mn a n

iterater : (Alternative mn, Monad mn) =>
           All (Parser toks tok mn (a -> a) :-> Parser toks tok mn a :-> Parser toks tok mn a)
iterater {toks} {tok} {mn} {a} = fix (RChain toks tok mn a) $ \ rec, op, val =>
                    alt (iteraterAux rec op val) val where

  iteraterAux : All (Box (RChain toks tok mn a) :-> RChain toks tok mn a)
  iteraterAux rec op val = MkParser $ \ mlen, ts =>
    runParser op mlen ts >>= \ sop =>
    let sopltn = lteTransitive (Small sop) mlen in
    let op'    = ltLower sopltn op in
    let val'   = ltLower sopltn val in
    runParser (call rec sopltn op' val') lteRefl (Leftovers sop) >>= \ res =>
    pure (ltLift (Small sop) (Success.map (Value sop) res))

hchainl : (Alternative mn, Monad mn) =>
          All (Parser toks tok mn a :-> Box (Parser toks tok mn (a -> b -> a)) :->
          Box (Parser toks tok mn b) :-> Parser toks tok mn a)
hchainl {toks} {tok} {mn} {a} {b} seed op arg =
  let ty   = Parser toks tok mn in
  let op'  = Box.map {a = ty (a -> b -> a)} (map flip) op in
  let arg' = duplicate arg in
  iteratel seed (map2 {a = ty (b -> a -> a)} app op' arg')

hchainr : (Alternative mn, Monad mn) =>
          All (Parser toks tok mn a :-> Box (Parser toks tok mn (a -> b -> b)) :->
               Parser toks tok mn b :-> Parser toks tok mn b)
hchainr arg op seed = iterater (app (map (flip apply) arg) op) seed

chainl1 : (Alternative mn, Monad mn) =>
          All (Parser toks tok mn a :-> Box (Parser toks tok mn (a -> a -> a)) :->
          Parser toks tok mn a)
chainl1 p op = hchainl p op p

chainr1 : (Alternative mn, Monad mn) =>
          All (Parser toks tok mn a :-> Box (Parser toks tok mn (a -> a -> a)) :->
          Parser toks tok mn a)
chainr1 p op = hchainr p op p

nelist : (Alternative mn, Monad mn) =>
         All (Parser toks tok mn a :-> Parser toks tok mn (NEList a))
nelist = fix _ $ \ rec, p => Combinators.map (uncurry consm) (andm p (Box.app rec p))
