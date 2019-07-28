module TParsec.Combinators

import Data.Nat
import Data.Maybe
import Util
import Relation.Indexed
import Induction.Nat as Box
import Data.Inspect
import Data.NEList
import TParsec.Success
import TParsec.Types

public export
lteLower : LTE m n -> Parser mn p a n -> Parser mn p a m
lteLower mlen p = MkParser (\plem => runParser p (lteTransitive plem mlen))

public export
ltLower : LT m n -> Parser mn p a n -> Parser mn p a m
ltLower = lteLower . lteSuccLeft

public export
box : {n : Nat} -> Parser mn p a n -> Box (Parser mn p a) n
box = lteClose lteLower

public export
anyTok : {p : Parameters mn} -> 
         (Alternative mn, Inspect (Toks p) (Tok p)) =>
         All (Parser mn p (Tok p))
anyTok = MkParser $ \_, ts =>
  choiceMap (\t => recordToken p (Success.Value t) *> pure t)
            (getTok {toks=Toks p} {tok=Tok p} ts)

public export
guardM : (Alternative mn, Monad mn) =>
         (a -> Maybe b) -> All (Parser mn p a :-> Parser mn p b)
guardM f p = MkParser $ \mlen, ts => do s <- runParser p mlen ts
                                        choiceMap pure (Success.guardM f s)

public export
guard : (Alternative mn, Monad mn) =>
        (a -> Bool) -> All (Parser mn p a :-> Parser mn p a)
guard p = guardM $ \v => toMaybe (p v) v

public export
maybeTok : {p : Parameters mn} -> 
           (Alternative mn, Monad mn, Inspect (Toks p) (Tok p)) =>
           (Tok p -> Maybe a) -> All (Parser mn p a)
maybeTok f = guardM f anyTok

public export
map : Functor mn =>
      (a -> b) -> All (Parser mn p a :-> Parser mn p b)
map f p = MkParser $ \le, ts => map (Success.map f) (runParser p le ts)

public export
cmap : Functor mn => b -> All (Parser mn p a :-> Parser mn p b)
cmap b = Combinators.map (\_ => b)

public export
fail : Alternative mn => All (Parser mn p a)
fail = MkParser $ \_, _ => empty

public export
alt : Alternative mn =>
      All (Parser mn p a :-> Parser mn p a :->
           Parser mn p a)
alt p q = MkParser $ \mlen, ts => runParser p mlen ts <|> runParser q mlen ts

public export
alts : Alternative mn =>
       All (List :. Parser mn p a :-> Parser mn p a)
alts = foldr alt fail

public export
andoptbind : (Monad mn, Alternative mn) =>
             All (Parser mn p a :-> (Cst a :-> Box (Parser mn p b)) :->
                  Parser mn p (a, Maybe b))
andoptbind p q = MkParser $ \mlen, ts =>
                 do sa <- runParser p mlen ts
                    let salen   = lteTransitive (Small sa) mlen
                    let combine = Success.map (map Just) . (Success.and sa)
                    (map combine (runParser (call (q (Value sa)) salen) lteRefl (Leftovers sa))) <|> pure (Success.map (flip MkPair Nothing) sa)

public export
andbind : Monad mn =>
          All (Parser mn p a :-> (Cst a :-> Box (Parser mn p b)) :->
               Parser mn p (a, b))
andbind p q = MkParser $ \mlen, ts =>
                do sa <- runParser p mlen ts
                   let salen  = lteTransitive (Small sa) mlen
                   let adjust = map (Success.and sa)
                   adjust (runParser (call (q (Value sa)) salen) lteRefl (Leftovers sa))

public export
andbindm : Monad mn =>
  All (Parser mn p a :-> Cst (a -> mn b) :-> Parser mn p (a, b))
andbindm p f = MkParser $ \mlen, ts => do ra <- runParser p mlen ts
                                          b <- f (Value ra)
                                          pure $ Success.map (flip MkPair b) ra

public export
landbindm : Monad mn =>
  All (Parser mn p a :-> Cst (a -> mn b) :-> Parser mn p a)
landbindm p f = map fst (andbindm p f)

public export
randbindm : Monad mn =>
  All (Parser mn p a :-> Cst (a -> mn b) :-> Parser mn p b)
randbindm p f = map snd (andbindm p f)

public export
and : Monad mn =>
      All (Parser mn p a :-> Box (Parser mn p b) :-> Parser mn p (a, b))
and p q = andbind p (\ _ => q)

public export
ands : Monad mn =>
       All (NEList :. Parser mn p a :-> Parser mn p (NEList a))
ands ps = NEList.foldr1 (\ p, ps => map (uncurry (<+>)) (and p (box ps))) (map (Combinators.map singleton) ps)

public export
andm : Monad mn =>
       All (Parser mn p a :-> Cst (mn b) :-> Parser mn p (a, b))
andm p q = MkParser $ \mlen, ts => do ra <- runParser p mlen ts
                                      b <- q
                                      pure $ Success.map (flip MkPair b) ra

public export
landm : Monad mn =>
        All (Parser mn p a :-> Cst (mn b) :-> Parser mn p a)
landm p q = map fst (andm p q)

public export
randm : Monad mn =>
        All (Parser mn p a :-> Cst (mn b) :-> Parser mn p b)
randm p q = map snd (andm p q)

public export
mand : Monad mn =>
       All (Cst (mn a) :-> Parser mn p b :-> Parser mn p (a, b))
mand p q = MkParser $ \mlen, ts => do a <- p
                                      map (Success.map (MkPair a)) (runParser q mlen ts)

public export
lmand : Monad mn =>
        All (Cst (mn a) :-> Parser mn p b :-> Parser mn p a)
lmand p q = map fst (mand p q)

public export
rmand : Monad mn =>
        All (Cst (mn a) :-> Parser mn p b :-> Parser mn p b)
rmand p q = map snd (mand p q)

public export
andopt : (Monad mn, Alternative mn) =>
         All (Parser mn p a :-> Box (Parser mn p b) :-> Parser mn p (a, Maybe b))
andopt p q = andoptbind p (\ _ => q)

public export
optand : (Monad mn, Alternative mn) =>
         All (Parser mn p a :-> Parser mn p b :-> Parser mn p (Maybe a, b))
optand p q = alt (and (map Just p) (box q)) (map (MkPair Nothing) q)

public export
bind : Monad mn =>
       All (Parser mn p a :-> (Cst a :-> Box (Parser mn p b)) :-> Parser mn p b)
bind p q = map snd (andbind p q)

public export
land : (Monad mn, Alternative mn) =>
       All (Parser mn p a :-> Box (Parser mn p b) :-> Parser mn p a)
land p q = map fst (and p q)

public export
rand : (Monad mn, Alternative mn) =>
       All (Parser mn p a :-> Box (Parser mn p b) :-> Parser mn p b)
rand p q = map snd (and p q)

public export
between : (Monad mn, Alternative mn) =>
          All (Parser mn p a :-> Box (Parser mn p c) :-> Box (Parser mn p b) :-> Parser mn p b)
between op cl p = land (rand op p) cl

public export
landopt : (Monad mn, Alternative mn) =>
          All (Parser mn p a :-> Box (Parser mn p b) :-> Parser mn p a)
landopt p q = map fst (andopt p q)

public export
randopt : (Monad mn, Alternative mn) =>
          All (Parser mn p a :-> Box (Parser mn p b) :-> Parser mn p (Maybe b))
randopt p q = map snd (andopt p q)

public export
loptand : (Monad mn, Alternative mn) =>
          All (Parser mn p a :-> Parser mn p b :-> Parser mn p (Maybe a))
loptand p q = map fst (optand p q)

public export
roptand : (Monad mn, Alternative mn) =>
          All (Parser mn p a :-> Parser mn p b :-> Parser mn p b)
roptand p q = map snd (optand p q)

public export
betweenopt : (Monad mn, Alternative mn) =>
             All (Parser mn p a :-> Box (Parser mn p c) :->
             Parser mn p b :-> Parser mn p b)
betweenopt op cl p = landopt (roptand op p) cl

public export
sum : Alternative mn =>
      All (Parser mn p a :-> Parser mn p b :-> Parser mn p (Either a b))
sum p q = alt (map Left p) (map Right q)

public export
app : Monad mn =>
      All (Parser mn p (a -> b) :-> Box (Parser mn p a) :-> Parser mn p b)
app p q = bind p (\ f => Box.map (Combinators.map f) q)

public export
exact : {p : Parameters mn} -> 
        (Alternative mn, Monad mn, Inspect (Toks p) (Tok p), Eq (Tok p)) =>
        Tok p -> All (Parser mn p (Tok p))
exact t = guard (\t' => t == t') anyTok

public export
exacts : {p : Parameters mn} -> 
         (Alternative mn, Monad mn, Inspect (Toks p) (Tok p), Eq (Tok p)) =>
         NEList (Tok p) -> All (Parser mn p (NEList (Tok p)))
exacts ts = ands (map (\t => exact t) ts)

public export
anyTokenBut : {p : Parameters mn} -> 
              (Alternative mn, Monad mn, Inspect (Toks p) (Tok p), Eq (Tok p)) =>
              Tok p -> All (Parser mn p (Tok p))
anyTokenBut t = guard (\t' => (t /= t')) anyTok

public export
noneOf : {p : Parameters mn} -> 
         (Alternative mn, Monad mn, Inspect (Toks p) (Tok p), Eq (Tok p)) =>
         List (Tok p) -> All (Parser mn p (Tok p))
noneOf ts = guard (\t' => all (/= t') ts) anyTok

public export
anyOf : {p : Parameters mn} -> 
        (Alternative mn, Monad mn, Inspect (Toks p) (Tok p), Eq (Tok p)) =>
        List (Tok p) -> All (Parser mn p (Tok p))
anyOf ts = alts (map (\t => exact t) ts)

public export
LChain : Parameters mn -> Type -> Nat -> Type
LChain p a n =
  Success (Toks p) a n -> Box (Parser mn p (a -> a)) n -> mn (Success (Toks p) a n)

public export
schainl : (Alternative mn, Monad mn) => All (LChain {mn} p a)
schainl = fix _ $ \rec, sa, op => schainlAux rec sa op <|> pure sa
  where
  schainlAux : All (Box (LChain {mn} p a) :-> LChain {mn} p a)
  schainlAux rec sa op = do sop <- runParser (call op (Small sa)) lteRefl (Leftovers sa)
                            let sa' = Success.map (\f => f (Success.Value sa)) sop
                            res <- call rec (Small sa) sa' (Box.ltLower (Small sa) op)
                            pure (ltLift (Small sa) res)
public export
iteratel : (Alternative mn, Monad mn) =>
           All (Parser mn p a :-> Box (Parser mn p (a -> a)) :-> Parser mn p a)
iteratel val op = MkParser $ \mlen, ts => do sa <- runParser val mlen ts
                                             schainl sa (Box.lteLower mlen op)
public export
RChain : Parameters mn -> Type -> Nat -> Type
RChain p {mn} a n =
  Parser mn p (a -> a) n -> Parser mn p a n -> Parser mn p a n

public export
iterater : (Alternative mn, Monad mn) =>
           All (Parser mn p (a -> a) :-> Parser mn p a :-> Parser mn p a)
iterater = fix _ $ \rec, op, val =>
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

public export
hchainl : (Alternative mn, Monad mn) =>
          All (Parser mn p a :-> Box (Parser mn p (a -> b -> a)) :->
          Box (Parser mn p b) :-> Parser mn p a)
hchainl seed op arg =
  let op'  = Box.map (Combinators.map flip) op
      arg' = duplicate arg
     in
  iteratel seed (map2 app op' arg')

public export
hchainr : (Alternative mn, Monad mn) =>
          All (Parser mn p a :-> Box (Parser mn p (a -> b -> b)) :->
               Parser mn p b :-> Parser mn p b)
hchainr arg op seed = iterater (app (map (flip apply) arg) op) seed

public export
chainl1 : (Alternative mn, Monad mn) =>
          All (Parser mn p a :-> Box (Parser mn p (a -> a -> a)) :->
          Parser mn p a)
chainl1 p op = hchainl p op (box p)

public export
chainr1 : (Alternative mn, Monad mn) =>
          All (Parser mn p a :-> Box (Parser mn p (a -> a -> a)) :->
          Parser mn p a)
chainr1 p op = hchainr p op p

public export
nelist : (Alternative mn, Monad mn) =>
         All (Parser mn p a :-> Parser mn p (NEList a))
nelist = fix (Parser mn p a :-> Parser mn p (NEList a)) $ \rec, p => 
  Combinators.map (uncurry consopt) (andopt p (Box.app rec (box p)))
