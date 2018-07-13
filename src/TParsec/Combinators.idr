module TParsec.Combinators

import Relation.Indexed
import Induction.Nat as Box
import Data.Inspect
import Data.NEList
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

anyTok : (Alternative mn, Inspect (Toks p) (Tok p)) =>
         All (Parser mn p (Tok p))
anyTok {p} = MkParser $ \_, ts =>
  choiceMap (\t => recordToken p (Value t) *> pure t)
            (getTok {toks=Toks p} {tok=Tok p} ts)

guardM : (Alternative mn, Monad mn) =>
         (a -> Maybe b) -> All (Parser mn p a :-> Parser mn p b)
guardM f p = MkParser $ \mlen, ts => do s <- runParser p mlen ts
                                        choiceMap pure (Success.guardM f s)

guard : (Alternative mn, Monad mn) =>
        (a -> Bool) -> All (Parser mn p a :-> Parser mn p a)
guard p = guardM $ \v => toMaybe (p v) v

maybeTok : (Alternative mn, Monad mn, Inspect (Toks p) (Tok p)) =>
           (Tok p -> Maybe a) -> All (Parser mn p a)
maybeTok p = guardM p anyTok

map : Functor mn =>
      (a -> b) -> All (Parser mn p a :-> Parser mn p b)
map f p = MkParser $ \le, ts => Functor.map (Success.map f) (runParser p le ts)

cmap : Functor mn => b -> All (Parser mn p a :-> Parser mn p b)
cmap b = map (\_ => b)

fail : Alternative mn => All (Parser mn p a)
fail = MkParser $ \_, _ => empty

alt : Alternative mn =>
      All (Parser mn p a :-> Parser mn p a :->
           Parser mn p a)
alt p q = MkParser $ \mlen, ts => runParser p mlen ts <|> runParser q mlen ts

alts : Alternative mn =>
       All (List :. Parser mn p a :-> Parser mn p a)
alts = foldr alt fail

andoptbind : (Monad mn, Alternative mn) =>
             All (Parser mn p a :-> (Cst a :-> Box (Parser mn p b)) :->
                  Parser mn p (a, Maybe b))
andoptbind p q = MkParser $ \mlen, ts =>
                 do sa <- runParser p mlen ts
                    let salen   = lteTransitive (Small sa) mlen
                    let combine = Success.map (Functor.map Just) . (Success.and sa)
                    (Functor.map combine (runParser (call (q (Value sa)) salen) lteRefl (Leftovers sa))) <|> pure (Success.map (flip MkPair Nothing) sa)

andbind : Monad mn =>
          All (Parser mn p a :-> (Cst a :-> Box (Parser mn p b)) :->
               Parser mn p (a, b))
andbind p q = MkParser $ \mlen, ts =>
                do sa <- runParser p mlen ts
                   let salen  = lteTransitive (Small sa) mlen
                   let adjust = Functor.map (Success.and sa)
                   adjust (runParser (call (q (Value sa)) salen) lteRefl (Leftovers sa))

and : Monad mn =>
      All (Parser mn p a :-> Box (Parser mn p b) :-> Parser mn p (a, b))
and p q = andbind p (\ _ => q)

ands : Monad mn =>
       All (NEList :. Parser mn p a :-> Parser mn p (NEList a))
ands ps = NEList.foldr1 (\ p, ps => map (uncurry (<+>)) (and p ps)) (Functor.map (map singleton) ps)

andm : Monad mn =>
       All (Parser mn p a :-> Cst (mn b) :-> Parser mn p (a, b))
andm p q = MkParser $ \mlen, ts => do ra <- runParser p mlen ts
                                      b <- q
                                      pure $ map (flip MkPair b) ra

landm : Monad mn =>
        All (Parser mn p a :-> Cst (mn b) :-> Parser mn p a)
landm p q = map fst (andm p q)

randm : Monad mn =>
        All (Parser mn p a :-> Cst (mn b) :-> Parser mn p b)
randm p q = map snd (andm p q)

mand : Monad mn =>
       All (Cst (mn a) :-> Parser mn p b :-> Parser mn p (a, b))
mand p q = MkParser $ \mlen, ts => do a <- p
                                      Functor.map (Success.map (MkPair a)) (runParser q mlen ts)

lmand : Monad mn =>
        All (Cst (mn a) :-> Parser mn p b :-> Parser mn p a)
lmand p q = map fst (mand p q)

rmand : Monad mn =>
        All (Cst (mn a) :-> Parser mn p b :-> Parser mn p b)
rmand p q = map snd (mand p q)

andopt : (Monad mn, Alternative mn) =>
         All (Parser mn p a :-> Box (Parser mn p b) :-> Parser mn p (a, Maybe b))
andopt p q = andoptbind p (\ _ => q)

optand : (Monad mn, Alternative mn) =>
         All (Parser mn p a :-> Parser mn p b :-> Parser mn p (Maybe a, b))
optand p q = alt (and (map Just p) q) (map (MkPair Nothing) q)

bind : Monad mn =>
       All (Parser mn p a :-> (Cst a :-> Box (Parser mn p b)) :-> Parser mn p b)
bind p q = map snd (andbind p q)

land : (Monad mn, Alternative mn) =>
       All (Parser mn p a :-> Box (Parser mn p b) :-> Parser mn p a)
land p q = map fst (and p q)

rand : (Monad mn, Alternative mn) =>
       All (Parser mn p a :-> Box (Parser mn p b) :-> Parser mn p b)
rand p q = map snd (and p q)

landopt : (Monad mn, Alternative mn) =>
          All (Parser mn p a :-> Box (Parser mn p b) :-> Parser mn p a)
landopt p q = map fst (andopt p q)

randopt : (Monad mn, Alternative mn) =>
          All (Parser mn p a :-> Box (Parser mn p b) :-> Parser mn p (Maybe b))
randopt p q = map snd (andopt p q)

loptand : (Monad mn, Alternative mn) =>
          All (Parser mn p a :-> Parser mn p b :-> Parser mn p (Maybe a))
loptand p q = map fst (optand p q)

roptand : (Monad mn, Alternative mn) =>
          All (Parser mn p a :-> Parser mn p b :-> Parser mn p b)
roptand p q = map snd (optand p q)

sum : Alternative mn =>
      All (Parser mn p a :-> Parser mn p b :-> Parser mn p (Either a b))
sum p q = alt (map Left p) (map Right q)

app : Monad mn =>
      All (Parser mn p (a -> b) :-> Box (Parser mn p a) :-> Parser mn p b)
app p q = bind p (\ f => Box.map (map f) q)

exact : (Alternative mn, Monad mn, Inspect (Toks p) (Tok p), Eq (Tok p)) =>
        Tok p -> All (Parser mn p (Tok p))
exact t = guard (\t' => t == t') anyTok

exacts : (Alternative mn, Monad mn, Inspect (Toks p) (Tok p), Eq (Tok p)) =>
         NEList (Tok p) -> All (Parser mn p (NEList (Tok p)))
exacts ts = ands (map (\t => exact t) ts)

anyOf : (Alternative mn, Monad mn, Inspect (Toks p) (Tok p), Eq (Tok p)) =>
        List (Tok p) -> All (Parser mn p (Tok p))
anyOf ts = alts (map (\t => exact t) ts)

between : (Monad mn, Alternative mn) =>
          All (Parser mn p a :-> Box (Parser mn p c) :->
          Box (Parser mn p b) :-> Parser mn p b)
between open close p = land (rand open p) close

betweenopt : (Monad mn, Alternative mn) =>
             All (Parser mn p a :-> Box (Parser mn p c) :->
             Parser mn p b :-> Parser mn p b)
betweenopt open close p = landopt (roptand open p) close

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

nelist : (Alternative mn, Monad mn) =>
         All (Parser mn p a :-> Parser mn p (NEList a))
nelist = fix _ $ \rec, p => Combinators.map (uncurry consopt) (andopt p (Box.app rec p))
