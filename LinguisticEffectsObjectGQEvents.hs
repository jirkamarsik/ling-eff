{-# LANGUAGE DeriveDataTypeable, DeriveFunctor #-} -- Useful for request types
{-# LANGUAGE FlexibleContexts #-} -- Necessary for effect contexts
{-# LANGUAGE TypeOperators #-} -- Necessary for types of handlers (:>)
{-# LANGUAGE TypeFamilies #-} -- Mapping from abstract types to semantic types
{-# LANGUAGE GADTs #-} -- Initial encoding of typed formulas
{-# LANGUAGE UndecidableInstances #-} -- Composition of type families

module LinguisticEffectsObjectGQEvents where

import Eff
import OpenUnion1
import Data.Typeable

import Control.Monad


newtype Entity = Entity String deriving (Eq, Typeable)

newtype Sym = Sym String deriving Eq

instance Show Sym where
  show (Sym name) = name

data Formula a where
  Var   :: Sym -> Formula a
  Abs   :: Sym -> Formula b -> Formula (a -> b)
  App   :: Formula (a -> b) -> Formula a -> Formula b

instance Show (Formula a) where
  show (Var (Sym var))      = var
  show (Abs (Sym var) body) = "(lambda (" ++ var ++ ") " ++ show body ++ ")"
  show (App f a)            = "(" ++ show f ++ " " ++ show a ++ ")"

type family EffTr r a
type instance EffTr r Bool = Eff r (Formula Bool)
type instance EffTr r Entity = Eff r (Formula Entity)
type instance EffTr r (a -> b) = (EffTr r a) -> (EffTr r b)


data AnaphoraTag = He | She | It

data Ref v = FreshR (Formula Entity -> v) |
             FetchR AnaphoraTag (Formula Entity -> v) |
             HangR Sym (() -> v)
             deriving (Typeable, Functor)

freshR :: (Member Ref r) => Eff r (Formula Entity)
freshR = send_req FreshR

fetchR :: (Member Ref r) => AnaphoraTag -> Eff r (Formula Entity)
fetchR tag = send_req (FetchR tag)

hangR :: (Member Ref r) => Sym -> Eff r ()
hangR var = send_req (HangR var)

data Event v = EventR (Formula Entity -> v)
               deriving (Typeable, Functor)

eventR :: (Member Event r) => Eff r (Formula Entity)
eventR = send_req EventR


select :: (Member Choose r) => AnaphoraTag -> [e] -> Eff r e
select tag = choose

runRef :: (Member Choose r, Member Fresh r) =>
          [Formula Entity] -> Eff (Ref :> r) (Formula Bool) -> Eff r (Formula Bool)
runRef rs m = loop rs (admin m) where
  loop rs (Val x) = return x
  loop rs (E u) = handle_relay u (loop rs) (handler rs)
  handler rs (FreshR k) = exists'' (\x -> do xv <- x
                                             loop (xv:rs) (k xv))
  handler rs (FetchR tag k) = do selected_ref <- select tag rs
                                 loop rs (k selected_ref)
  handler rs (HangR var k) = fmap existsF (fill var (\x -> do xv <- x
                                                              loop (xv:rs) (k ())))

enter :: (Member Choose r, Member Fresh r, Member Ref r) =>
         Eff r (Formula Bool) -> Eff r (Formula Bool)
enter m = loop [] (admin m) where
  loop rs (Val x) = return x
  loop rs (E u) = interpose u (loop rs) (handler rs)
  handler rs (FreshR k) = exists'' (\x -> do xv <- x
                                             loop (xv:rs) (k xv))
  handler rs (FetchR tag k) = do selected_ref <- select tag rs `mplus'` fetchR tag
                                 loop rs (k selected_ref)
  handler rs (HangR var k) = fmap existsF (fill var (\x -> do xv <- x
                                                              loop (xv:rs) (k ())))


supplyEvent :: Formula Entity -> Eff (Event :> r) a -> Eff r a
supplyEvent e = (continueSupplyEvent e) . admin

continueSupplyEvent :: Formula Entity -> VE a (Event :> r) -> Eff r a
continueSupplyEvent e m = loop m where
  loop (Val x) = return x
  loop (E u) = handle_relay u loop handler
  handler (EventR k) = loop (k e)

ec_extra :: (Member Ref r) =>
            Eff (Event :> r) (Formula Bool) -> Eff r (Formula Bool)
ec_extra m = do e <- freshR
                supplyEvent e m

ec_composed :: (Member Ref r) =>
               Eff (Event :> r) (Formula Bool) -> Eff r (Formula Bool)
ec_composed m = loop (admin m) where
  loop (Val x) = return x
  loop (E u) = handle_relay u loop handler
  handler (EventR k) = do e <- freshR
                          continueSupplyEvent e (k e)

ec_stateful :: (Member Ref r) =>
               Eff (Event :> r) (Formula Bool) -> Eff r (Formula Bool)
ec_stateful m = loop Nothing (admin m) where
  loop event (Val x) = return x
  loop event (E u) = handle_relay u (loop event) (handler event)
  handler Nothing (EventR k) = do e <- freshR
                                  loop (Just e) (k e)
  handler (Just e) (EventR k) = loop (Just e) (k e)

ec_final :: (Member Ref r, Member Fresh r) =>
            Eff (Event :> r) (Formula Bool) -> Eff r (Formula Bool)
ec_final m = loop Nothing (admin m) where
  loop Nothing (Val x) = return x
  loop (Just (Var var)) (Val x) = hangR var >> return x
  loop event (E u) = handle_relay u (loop event) (handler event)
  handler Nothing (EventR k) = do n <- fresh
                                  let e = Var (Sym ("e" ++ show n))
                                  loop (Just e) (k e)
  handler (Just e) (EventR k) = loop (Just e) (k e)

ec :: (Member Ref r, Member Fresh r) =>
      Eff (Event :> r) (Formula Bool) -> Eff r (Formula Bool)
ec = ec_final

supplyNewEvent :: (Member Event r) => Formula Entity -> Eff r a -> Eff r a
supplyNewEvent e = (continueSupplyNewEvent e) . admin

continueSupplyNewEvent :: (Member Event r) => Formula Entity -> VE a r -> Eff r a
continueSupplyNewEvent e m = loop m where
  loop (Val x) = return x
  loop (E u) = interpose u loop handler
  handler (EventR k) = loop (k e)

scopeDomain_old :: (Member Ref r, Member Event r) => Eff r a -> Eff r a
scopeDomain_old m = loop (admin m) where
  loop (Val x) = return x
  loop (E u) = interpose u loop handler
  handler (EventR k) = do e <- freshR
                          continueSupplyNewEvent e (k e)

scopeDomain_final :: (Member Ref r, Member Fresh r, Member Event r) =>
                     Eff r (Formula Bool) -> Eff r (Formula Bool)
scopeDomain_final m = loop Nothing (admin m) where
  loop Nothing (Val x) = return x
  loop (Just (Var var)) (Val x) = hangR var >> return x
  loop event (E u) = interpose u (loop event) (handler event)
  handler Nothing (EventR k) = do n <- fresh
                                  let e = Var (Sym ("e" ++ show n))
                                  loop (Just e) (k e)
  handler (Just e) (EventR k) = loop (Just e) (k e)

scopeDomain :: (Member Ref r, Member Fresh r, Member Event r) =>
               Eff r (Formula Bool) -> Eff r (Formula Bool)
scopeDomain = scopeDomain_final

abstractOutEvent :: (Member Event r) =>
                    Eff r a -> Eff r (Formula Entity) -> Eff r a
abstractOutEvent m e = e >>= (\ev -> supplyNewEvent ev m)

makeEventClosure :: (Member Fresh r, Member Event r) =>
                    Eff r (Formula a) -> Eff r (Formula (Entity -> a))
makeEventClosure = fillFresh . abstractOutEvent

sumEvent :: (Member Event r, Member Fresh r) =>
            Eff r (Formula Bool) -> Eff r (Formula Bool)
sumEvent m = eventR `eq''` liftFM (Sym "sum") (makeEventClosure m)

subEvent :: (Member Event r, Member Ref r) =>
            Eff r (Formula Bool) -> Eff r (Formula Bool)
subEvent m = do e_sup <- eventR
                e_inf <- freshR
                and'' (return (liftF2 (Sym "part-of") e_inf e_sup))
                      (supplyNewEvent e_inf m)


-- SEMANTICS

liftF :: Sym -> Formula a -> Formula b
liftF f x = App (Var f) x

liftF2 :: Sym -> Formula a -> Formula b -> Formula c
liftF2 f x y = App (App (Var f) x) y

liftF3 :: Sym -> Formula a -> Formula b -> Formula c -> Formula d
liftF3 f x y z = App (App (App (Var f) x) y) z

liftFM :: Sym -> Eff r (Formula a) -> Eff r (Formula b)
liftFM = liftM . liftF

liftFM2 :: Sym -> Eff r (Formula a) -> Eff r (Formula b) -> Eff r (Formula c)
liftFM2 = liftM2 . liftF2

liftFM3 :: Sym -> Eff r (Formula a) -> Eff r (Formula b) -> Eff r (Formula c)
           -> Eff r (Formula d)
liftFM3 = liftM3 . liftF3

fill :: Sym -> (Eff r (Formula a) -> Eff r (Formula b)) -> Eff r (Formula (a -> b))
fill var f = do body <- f (return (Var var))
                return (Abs var body)

fillFresh :: (Member Fresh r) =>
             (Eff r (Formula a) -> Eff r (Formula b)) -> Eff r (Formula (a -> b))
fillFresh f = do n <- fresh
                 let var = Sym ("x" ++ show n)
                 fill var f

existsF :: Formula (Entity -> Bool) -> Formula Bool
existsF = liftF (Sym "exists")

exists' :: (Member Fresh r) => EffTr r ((Entity -> Bool) -> Bool)
exists' p = fmap existsF (fillFresh p)

exists'' :: (Member Fresh r) => EffTr r ((Entity -> Bool) -> Bool)
exists'' = exists'

forallF :: Formula (Entity -> Bool) -> Formula Bool
forallF = liftF (Sym "forall")

forall' :: (Member Fresh r) => EffTr r ((Entity -> Bool) -> Bool)
forall' p = fmap forallF (fillFresh p)

forall'' :: (Member Ref r, Member Fresh r, Member Choose r, Member Event r)
            => EffTr r ((Entity -> Bool) -> Bool)
forall'' p = not'' (exists'' (not'' . p))

andF :: Formula Bool -> Formula Bool -> Formula Bool
andF = liftF2 (Sym "and")

and' :: EffTr r (Bool -> Bool -> Bool)
and' = liftM2 andF

and'' :: EffTr r (Bool -> Bool -> Bool)
and'' x y = x `and'` y

notF :: Formula Bool -> Formula Bool
notF = liftF (Sym "not")

not' :: EffTr r (Bool -> Bool)
not' = liftM notF

not'' :: (Member Ref r, Member Fresh r, Member Choose r, Member Event r) =>
         EffTr r (Bool -> Bool)
not'' = not' . enter

eqF :: Formula Entity -> Formula Entity -> Formula Bool
eqF = liftF2 (Sym "=")

eq' :: EffTr r (Entity -> Entity -> Bool)
eq' = liftM2 eqF

eq'' :: EffTr r (Entity -> Entity -> Bool)
eq'' = eq'

orF :: Formula Bool -> Formula Bool -> Formula Bool
orF = liftF2 (Sym "or")

or' :: EffTr r (Bool -> Bool -> Bool)
or' = liftM2 orF

or'' :: (Member Ref r, Member Fresh r, Member Choose r, Member Event r) =>
        EffTr r (Bool -> Bool -> Bool)
or'' x y = not'' (not'' x `and''` not'' y)

implF :: Formula Bool -> Formula Bool -> Formula Bool
implF = liftF2 (Sym "impl")

impl' :: EffTr r (Bool -> Bool -> Bool)
impl' = liftM2 implF

impl'' :: (Member Ref r, Member Fresh r, Member Choose r, Member Event r) =>
          EffTr r (Bool -> Bool -> Bool)
impl'' x y = not'' (x `and''` not'' y)


-- SYNTAX

data M
data S
data NP
data N

type family SemTr a
type instance SemTr M        = Bool
type instance SemTr S        = Bool
type instance SemTr NP       = GQ
type instance SemTr N        = Entity -> Bool
type instance SemTr (a -> b) = SemTr a -> SemTr b

type VP = NP -> S
type GQ = (Entity -> Bool) -> Bool

type family SemEffTr r a
type instance SemEffTr r a = EffTr r (SemTr a)


john :: (Member Ref r) => SemEffTr r NP
john s = do j <- freshR
            (return (j `eqF` Var (Sym "john"))) `and''` s (return j)

mary :: (Member Ref r) => SemEffTr r NP
mary s = do m <- freshR
            (return (m `eqF` Var (Sym "mary"))) `and''` s (return m)

farmer :: SemEffTr r N
farmer = liftFM (Sym "farmer")

donkey :: SemEffTr r N
donkey = liftFM (Sym "donkey")

mkTVSWS :: (Member Event r) => Sym -> SemEffTr r (NP -> VP)
mkTVSWS var o s = s (\x -> o (\y -> liftFM3 (Sym "owns") eventR x y))

mkTVOWS :: (Member Event r) => Sym -> SemEffTr r (NP -> VP)
mkTVOWS var o s = o (\y -> s (\x -> liftFM3 (Sym "owns") eventR x y))

ownsOWS :: (Member Event r) => SemEffTr r (NP -> VP)
ownsSWS = mkTVSWS (Sym "owns")

ownsSWS :: (Member Event r) => SemEffTr r (NP -> VP)
ownsOWS = mkTVOWS (Sym "owns")

owns :: (Member Event r, Member Choose r) => SemEffTr r (NP -> VP)
owns o s = ownsSWS o s `mplus'` ownsOWS o s

beatsSWS :: (Member Event r) => SemEffTr r (NP -> VP)
beatsSWS = mkTVSWS (Sym "beats")

beatsOWS :: (Member Event r) => SemEffTr r (NP -> VP)
beatsOWS = mkTVOWS (Sym "beats")

beats :: (Member Event r, Member Choose r) => SemEffTr r (NP -> VP)
beats o s = beatsSWS o s `mplus'` beatsOWS o s

lovesSWS :: (Member Event r) => SemEffTr r (NP -> VP)
lovesSWS = mkTVSWS (Sym "loves")

lovesOWS :: (Member Event r) => SemEffTr r (NP -> VP)
lovesOWS = mkTVOWS (Sym "loves")

loves :: (Member Event r, Member Choose r) => SemEffTr r (NP -> VP)
loves o s = lovesSWS o s `mplus'` lovesOWS o s

slowly :: (Member Event r) => SemEffTr r (VP -> VP)
slowly p x = liftFM (Sym "slow") eventR `and''` p x

it :: (Member Ref r) => SemEffTr r NP 
it s = s (fetchR It)

he :: (Member Ref r) => SemEffTr r NP 
he s = s (fetchR He)

she :: (Member Ref r) => SemEffTr r NP
she s = s (fetchR She)

who :: (Member Ref r, Member Fresh r, Member Event r) =>
       SemEffTr r ((NP -> S) -> N -> N)
who r n x = n x `and''` (scopeDomain (r (\p -> p x)))

a :: (Member Ref r) => SemEffTr r (N -> NP)
a n s = do x <- freshR
           n (return x) `and''` s (return x)

every :: (Member Ref r, Member Choose r, Member Fresh r, Member Event r) =>
         SemEffTr r (N -> NP)
every n s = not'' (do x <- freshR
                      n (return x) `and''` not'' (subEvent (s (return x))))

eos :: (Member Ref r, Member Fresh r) =>
       SemEffTr (Event :> r) S -> SemEffTr r M
eos = ec

next :: SemEffTr r (M -> M -> M)
next = and''


runAll' rs = run . (flip runFresh) 0 . makeChoice . runRef rs
runAll = runAll' []

donkeySentence = eos $ beatsSWS it (every (who (ownsSWS (a donkey)) farmer))
donkeySentenceR = runAll donkeySentence

johnBeatsADonkey = eos $ beatsSWS (a donkey) john
johnBeatsADonkeyR = runAll johnBeatsADonkey

heBeatsIt = eos (beatsSWS it he)
heBeatsItR = runAll heBeatsIt

dsANDhbi = donkeySentence `next` heBeatsIt
dsANDhbiR = runAll dsANDhbi

jbadANDhbi = johnBeatsADonkey `next` heBeatsIt
jbadANDhbiR = runAll jbadANDhbi

every_a = eos $ beats (a donkey) (every farmer)
every_aR = runAll every_a

eaANDhbi = every_a `next` heBeatsIt
eaANDhbiR = runAll eaANDhbi

johnLovesIt = eos $ lovesSWS it john
johnLovesItR = runAll johnLovesIt

slowlySent = eos $ slowly (beatsSWS john) (a farmer)
slowlySentR = runAll slowlySent
