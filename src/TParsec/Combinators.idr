module TParsec.Combinators

import Relation.Indexed
import Induction.Nat as Box
import Data.Inspect
import Data.NEList
import TParsec.Success
import TParsec.Types
import TParsec.Instruments

%default total
%access public export

lteLower : LTE m n -> Parser p mn a n -> Parser p mn a m
lteLower mlen p = MkParser (\plem => runParser p (lteTransitive plem mlen))

ltLower : LT m n -> Parser p mn a n -> Parser p mn a m
ltLower mltn = lteLower (lteSuccLeft mltn)

implicit 
box : Parser p mn a n -> Box (Parser p mn a) n
box = lteClose lteLower

anyTok : (Alternative mn, Instrumented p mn, Inspect (Toks p) (Tok p)) =>
         All (Parser p mn (Tok p))
anyTok {p} = MkParser (\mlen, ts => 
  choiceMap (\t => recordToken {p} (Value t) *> pure t) 
            (getTok {toks=Toks p} {tok=Tok p} ts))

guardM : (Alternative mn, Monad mn) =>
         (a -> Maybe b) -> All (Parser p mn a :-> Parser p mn b)
guardM f p = MkParser $ \mlen, ts => do s <- runParser p mlen ts
                                        choiceMap pure (Success.guardM f s)

guard : (Alternative mn, Monad mn) =>
        (a -> Bool) -> All (Parser p mn a :-> Parser p mn a)
guard p = guardM $ \v => toMaybe (p v) v

maybeTok : (Alternative mn, Monad mn, Instrumented p mn, Inspect (Toks p) (Tok p)) =>
           (Tok p -> Maybe a) -> All (Parser p mn a)
maybeTok p = guardM p anyTok

map : Functor mn =>
      (a -> b) -> All (Parser p mn a :-> Parser p mn b)
map f p = MkParser $ \le, ts => Functor.map (Success.map f) (runParser p le ts)

cmap : Functor mn => b -> All (Parser p mn a :-> Parser p mn b)
cmap b = map (\_ => b)

fail : Alternative mn => All (Parser p mn a)
fail = MkParser $ \_, _ => empty

alt : Alternative mn =>
      All (Parser p mn a :-> Parser p mn a :->
           Parser p mn a)
alt p q = MkParser $ \mlen, ts => runParser p mlen ts <|> runParser q mlen ts

alts : Alternative mn =>
       All (List :. Parser p mn a :-> Parser p mn a)
alts = foldr alt fail

andmbind : (Monad mn, Alternative mn) =>
           All (Parser p mn a :-> (Cst a :-> Box (Parser p mn b)) :->
                Parser p mn (a, Maybe b))
andmbind p q = MkParser $ \mlen, ts =>
                 do sa <- runParser p mlen ts
                    let salen   = lteTransitive (Small sa) mlen
                    let combine = Success.map (Functor.map Just) . (Success.and sa)
                    (Functor.map combine (runParser (call (q (Value sa)) salen) lteRefl (Leftovers sa))) <|> pure (Success.map (flip MkPair Nothing) sa)

andbind : Monad mn =>
           All (Parser p mn a :-> (Cst a :-> Box (Parser p mn b)) :->
                Parser p mn (a, b))
andbind p q = MkParser $ \mlen, ts =>
                do sa <- runParser p mlen ts
                   let salen  = lteTransitive (Small sa) mlen
                   let adjust = Functor.map (Success.and sa)
                   adjust (runParser (call (q (Value sa)) salen) lteRefl (Leftovers sa))

and : Monad mn =>
      All (Parser p mn a :-> Box (Parser p mn b) :-> Parser p mn (a, b))
and p q = andbind p (\ _ => q)

ands : Monad mn =>
       All (NEList :. Parser p mn a :-> Parser p mn (NEList a))
ands ps = NEList.foldr1 (\ p, ps => map (uncurry (<+>)) (and p ps)) (Functor.map (map singleton) ps)

andm : (Monad mn, Alternative mn) =>
       All (Parser p mn a :-> Box (Parser p mn b) :->
       Parser p mn (a, Maybe b))
andm p q = andmbind p (\ _ => q)

mand : (Monad mn, Alternative mn) =>
       All (Parser p mn a :-> Parser p mn b :-> Parser p mn (Maybe a, b))
mand p q = alt (and (map Just p) q) (map (MkPair Nothing) q)

bind : Monad mn =>
       All (Parser p mn a :-> (Cst a :-> Box (Parser p mn b)) :-> Parser p mn b)
bind p q = map snd (andbind p q)

land : (Monad mn, Alternative mn) =>
       All (Parser p mn a :-> Box (Parser p mn b) :-> Parser p mn a)
land p q = map fst (and p q)

rand : (Monad mn, Alternative mn) =>
       All (Parser p mn a :-> Box (Parser p mn b) :-> Parser p mn b)
rand p q = map snd (and p q)

landm : (Monad mn, Alternative mn) =>
        All (Parser p mn a :-> Box (Parser p mn b) :-> Parser p mn a)
landm p q = map fst (andm p q)

randm : (Monad mn, Alternative mn) =>
        All (Parser p mn a :-> Box (Parser p mn b) :-> Parser p mn (Maybe b))
randm p q = map snd (andm p q)

lmand : (Monad mn, Alternative mn) =>
        All (Parser p mn a :-> Parser p mn b :-> Parser p mn (Maybe a))
lmand p q = map fst (mand p q)

rmand : (Monad mn, Alternative mn) =>
        All (Parser p mn a :-> Parser p mn b :-> Parser p mn b)
rmand p q = map snd (mand p q)

sum : Alternative mn =>
      All (Parser p mn a :-> Parser p mn b :-> Parser p mn (Either a b))
sum p q = alt (map Left p) (map Right q)

app : Monad mn =>
      All (Parser p mn (a -> b) :-> Box (Parser p mn a) :-> Parser p mn b)
app p q = bind p (\ f => Box.map (map f) q)

exact : (Alternative mn, Monad mn, Instrumented p mn, Inspect (Toks p) (Tok p), Eq (Tok p)) =>
        Tok p -> All (Parser p mn (Tok p))
exact t = guard (\t' => t == t') anyTok

exacts : (Alternative mn, Monad mn, Instrumented p mn, Inspect (Toks p) (Tok p), Eq (Tok p)) =>
         NEList (Tok p) -> All (Parser p mn (NEList (Tok p)))
exacts ts = ands (map (\t => exact t) ts)

anyOf : (Alternative mn, Monad mn, Instrumented p mn, Inspect (Toks p) (Tok p), Eq (Tok p)) =>
        List (Tok p) -> All (Parser p mn (Tok p))
anyOf ts = alts (map (\t => exact t) ts)

between : (Monad mn, Alternative mn) =>
          All (Parser p mn a :-> Box (Parser p mn c) :->
          Box (Parser p mn b) :-> Parser p mn b)
between open close p = land (rand open p) close

betweenm : (Monad mn, Alternative mn) =>
           All (Parser p mn a :-> Box (Parser p mn c) :->
           Parser p mn b :-> Parser p mn b)
betweenm open close p = landm (rmand open p) close

LChain : Parameters -> (Type -> Type) -> Type -> Nat -> Type
LChain p mn a n =
  Success (Toks p) a n -> Box (Parser p mn (a -> a)) n -> mn (Success (Toks p) a n)

schainl : (Alternative mn, Monad mn) => All (LChain p mn a)
schainl {mn} {a} = fix _ $ \rec, sa, op => schainlAux rec sa op <|> pure sa 
  where
  schainlAux : All (Box (LChain p mn a) :-> LChain p mn a)
  schainlAux rec sa op = do sop <- runParser (call op (Small sa)) lteRefl (Leftovers sa) 
                            let sa' = Success.map (\f => f (Value sa)) sop
                            res <- call rec (Small sa) sa' (Box.ltLower (Small sa) op)
                            pure (ltLift (Small sa) res)

iteratel : (Alternative mn, Monad mn) =>
           All (Parser p mn a :-> Box (Parser p mn (a -> a)) :-> Parser p mn a)
iteratel val op = MkParser $ \mlen, ts => do sa <- runParser val mlen ts
                                             schainl sa (Box.lteLower mlen op)

RChain : Parameters -> (Type -> Type) -> Type -> Nat -> Type
RChain p mn a n =
  Parser p mn (a -> a) n -> Parser p mn a n -> Parser p mn a n

iterater : (Alternative mn, Monad mn) =>
           All (Parser p mn (a -> a) :-> Parser p mn a :-> Parser p mn a)
iterater {mn} {p} {a} = fix (RChain p mn a) $ \rec, op, val =>
                                     alt (iteraterAux rec op val) val 
  where
  iteraterAux : All (Box (RChain p mn a) :-> RChain p mn a)
  iteraterAux rec op val = MkParser $ \mlen, ts =>
    do sop <- runParser op mlen ts 
       let sopltn = lteTransitive (Small sop) mlen 
       let op'    = ltLower sopltn op 
       let val'   = ltLower sopltn val 
       res <- runParser (call rec sopltn op' val') lteRefl (Leftovers sop)
       pure (ltLift (Small sop) (Success.map (Value sop) res))

hchainl : (Alternative mn, Monad mn) =>
          All (Parser p mn a :-> Box (Parser p mn (a -> b -> a)) :->
          Box (Parser p mn b) :-> Parser p mn a)
hchainl {p} {mn} {a} {b} seed op arg =
  let ty   = Parser p mn 
      op'  = Box.map {a = ty (a -> b -> a)} (map flip) op 
      arg' = duplicate arg 
     in
  iteratel seed (map2 {a = ty (b -> a -> a)} app op' arg')

hchainr : (Alternative mn, Monad mn) =>
          All (Parser p mn a :-> Box (Parser p mn (a -> b -> b)) :->
               Parser p mn b :-> Parser p mn b)
hchainr arg op seed = iterater (app (map (flip apply) arg) op) seed

chainl1 : (Alternative mn, Monad mn) =>
          All (Parser p mn a :-> Box (Parser p mn (a -> a -> a)) :->
          Parser p mn a)
chainl1 p op = hchainl p op p

chainr1 : (Alternative mn, Monad mn) =>
          All (Parser p mn a :-> Box (Parser p mn (a -> a -> a)) :->
          Parser p mn a)
chainr1 p op = hchainr p op p

nelist : (Alternative mn, Monad mn) =>
         All (Parser p mn a :-> Parser p mn (NEList a))
nelist = fix _ $ \rec, p => Combinators.map (uncurry consm) (andm p (Box.app rec p))
