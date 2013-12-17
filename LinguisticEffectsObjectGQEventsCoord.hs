{-# LANGUAGE DeriveDataTypeable, DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}

module LinguisticEffectsObjectGQEventsCoord where

import Eff
import OpenUnion1
import Data.Typeable

import Control.Monad


newtype Entity = Entity String deriving (Eq, Typeable)

newtype Sym = Sym String

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
             FetchR AnaphoraTag (Formula Entity -> v)
             deriving (Typeable, Functor)

freshR :: (Member Ref r) => Eff r (Formula Entity)
freshR = send_req FreshR

fetchR :: (Member Ref r) => AnaphoraTag -> Eff r (Formula Entity)
fetchR tag = send_req (FetchR tag)

data Event v = EventR (Formula Entity -> v)
               deriving (Typeable, Functor)

eventR :: (Member Event r) => Eff r (Formula Entity)
eventR = send_req EventR

data CoordOp = Conj | Disj
data CoordPol = Pos | Neg
data CoordMode = CoordMode CoordOp CoordPol

data Coord v = forall a. Coord CoordMode a a (a -> v)
               deriving Typeable

instance Functor Coord where
  fmap f (Coord mode x y k) = Coord mode x y (f . k)

coord :: (Member Coord r) => CoordMode -> a -> a -> Eff r a
coord mode x y = send_req (Coord mode x y)


select :: (Member Choose r) => AnaphoraTag -> [e] -> Eff r e
select tag = choose

runRef :: (Member Choose r, Member Fresh r) =>
          [Formula Entity] -> Eff (Ref :> r) (Formula Bool) -> Eff r (Formula Bool)
runRef rs m = loop rs (admin m) where
  loop rs (Val x) = return x
  loop rs (E u) = handle_relay u (loop rs) (handler rs)
  handler rs (FreshR k) = exists' (\x -> do xv <- x
                                            loop (xv:rs) (k xv))
  handler rs (FetchR tag k) = do selected_ref <- select tag rs
                                 loop rs (k selected_ref)

enter :: (Member Choose r, Member Fresh r, Member Ref r) =>
         Eff r (Formula Bool) -> Eff r (Formula Bool)
enter m = loop [] (admin m) where
  loop rs (Val x) = return x
  loop rs (E u) = interpose u (loop rs) (handler rs)
  handler rs (FreshR k) = exists' (\x -> do xv <- x
                                            loop (xv:rs) (k xv))
  handler rs (FetchR tag k) = do selected_ref <- select tag rs `mplus'` fetchR tag
                                 loop rs (k selected_ref)


ec :: (Member Fresh r, Member Ref r) =>
      Eff (Event :> r) (Formula Bool) -> Eff r (Formula Bool)
ec m = do e <- freshR
          let loop (Val x) = return x
              loop (E u) = handle_relay u loop handler
              handler (EventR k) = loop (k e)
          loop (admin m)

scopeDomain :: (Member Fresh r, Member Event r, Member Ref r) =>
               Eff r (Formula Bool) -> Eff r (Formula Bool)
scopeDomain m = do e <- freshR
                   let loop (Val x) = return x
                       loop (E u) = interpose u loop handler
                       handler (EventR k) = loop (k e)
                   loop (admin m)


runCoord :: (Member Choose r, Member Fresh r, Member Ref r, Member Event r) =>
            Eff (Coord :> r) (Formula Bool) -> Eff r (Formula Bool)
runCoord m = loop (admin m) where
  loop (Val x) = return x
  loop (E u) = handle_relay u loop handler
  handler (Coord (CoordMode op pol) x y k) =
    polf (loop (k x)) `opf` polf (loop (k y))
    where opf = case op of Conj -> and''
                           Disj -> or''
          polf = case pol of Pos -> id
                             Neg -> not''

negateMode :: CoordMode -> CoordMode
negateMode (CoordMode op pol) = CoordMode op' pol' where
  op' = case op of
    Conj -> Disj
    Disj -> Conj
  pol' = case pol of
    Pos -> Neg
    Neg -> Pos

switchPolarity :: (Member Choose r, Member Fresh r, Member Ref r,
                   Member Coord r, Member Event r) =>
                  Eff r a -> Eff r a 
switchPolarity m = loop (admin m) where
  loop (Val x) = return x
  loop (E u) = interpose u loop handler
  handler (Coord mode x y k) = do one <- coord (negateMode mode) x y
                                  loop $ k one

     
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

fill :: (Member Fresh r) =>
        (Eff r (Formula a) -> Eff r (Formula b)) -> Eff r (Formula (a -> b))
fill f = do n <- fresh
            let var = Sym ("x" ++ show n)
            body <- f (return (Var var))
            return (Abs var body)

exists' :: (Member Fresh r) => EffTr r ((Entity -> Bool) -> Bool)
exists' p = fmap (App (Var (Sym "exists"))) (fill p)

andF :: Formula Bool -> Formula Bool -> Formula Bool
andF = liftF2 (Sym "and")

and' :: EffTr r (Bool -> Bool -> Bool)
and' = liftM2 andF

and'' :: (Member Ref r, Member Event r, Member Fresh r) =>
         EffTr r (Bool -> Bool -> Bool)
and'' x y = x `and'` y

notF :: Formula Bool -> Formula Bool
notF = liftF (Sym "not")

not' :: EffTr r (Bool -> Bool)
not' = liftM notF

not'' :: (Member Ref r, Member Fresh r, Member Choose r, Member Event r,
          Member Coord r) =>
         EffTr r (Bool -> Bool)
not'' = not' . enter . switchPolarity

eqF :: Formula Entity -> Formula Entity -> Formula Bool
eqF = liftF2 (Sym "=")

eq' :: EffTr r (Entity -> Entity -> Bool)
eq' = liftM2 eqF

orF :: Formula Bool -> Formula Bool -> Formula Bool
orF = liftF2 (Sym "or")

or' :: EffTr r (Bool -> Bool -> Bool)
or' = liftM2 orF

or'' :: (Member Choose r, Member Fresh r, Member Ref r, Member Event r,
         Member Coord r) =>
        EffTr r (Bool -> Bool -> Bool)
or'' x y = not'' (not'' x `and''` not'' y)


-- SYNTAX

type GQ = (Entity -> Bool) -> Bool

john :: (Member Ref r) => EffTr r GQ
john s = do j <- freshR
            (return (j `eqF` Var (Sym "john"))) `and'` s (return j)

mary :: (Member Ref r) => EffTr r GQ
mary s = do m <- freshR
            (return (m `eqF` Var (Sym "mary"))) `and'` s (return m)

farmer :: EffTr r (Entity -> Bool)
farmer = liftFM (Sym "farmer")

donkey :: EffTr r (Entity -> Bool)
donkey = liftFM (Sym "donkey")

ownsSWS :: (Member Event r) => EffTr r (GQ -> GQ -> Bool)
ownsSWS o s = s (\x -> o (\y -> liftFM3 (Sym "owns") eventR x y))

ownsOWS :: (Member Event r) => EffTr r (GQ -> GQ -> Bool)
ownsOWS o s = o (\y -> s (\x -> liftFM3 (Sym "owns") eventR x y))

beatsSWS :: (Member Event r) => EffTr r (GQ -> GQ -> Bool)
beatsSWS o s = s (\x -> o (\y -> liftFM3 (Sym "beats") eventR x y))

beatsOWS :: (Member Event r) => EffTr r (GQ -> GQ -> Bool)
beatsOWS o s = o (\y -> s (\x -> liftFM3 (Sym "beats") eventR x y))

slowly :: (Member Event r) => EffTr r ((GQ -> Bool) -> (GQ -> Bool))
slowly p x = liftFM (Sym "slow") eventR `and'` p x

it :: (Member Ref r) => EffTr r GQ
it s = s (fetchR It)

he :: (Member Ref r) => EffTr r GQ 
he s = s (fetchR He)

she :: (Member Ref r) => EffTr r GQ 
she s = s (fetchR She)

who :: (Member Event r, Member Fresh r, Member Ref r) =>
       EffTr r ((GQ -> Bool) -> (Entity -> Bool) -> (Entity -> Bool))
who r n x = n x `and'` (scopeDomain (r (\p -> p x)))

a :: (Member Ref r) => EffTr r ((Entity -> Bool) -> GQ)
a n s = do x <- freshR
           n (return x) `and'` s (return x)

every :: (Member Ref r, Member Choose r, Member Fresh r, Member Event r,
          Member Coord r) =>
         EffTr r ((Entity -> Bool) -> GQ)
every n s = notH (do x <- freshR
                     n (return x) `and'` notH (scopeDomain (s (return x))))
            where notH = not' . enter

and_NP :: (Member Coord r) => EffTr r (GQ -> GQ -> GQ)
and_NP f1 f2 = \x -> do f <- coord (CoordMode Conj Pos) f1 f2
                        f x

and_VP :: (Member Coord r) =>
          EffTr r ((Entity -> Bool) -> (Entity -> Bool) -> (Entity -> Bool))
and_VP f1 f2 = \x -> do f <- coord (CoordMode Conj Pos) f1 f2
                        f x

or_NP :: (Member Coord r) => EffTr r (GQ -> GQ -> GQ)
or_NP f1 f2 = \x -> do f <- coord (CoordMode Disj Pos) f1 f2
                       f x

or_VP :: (Member Coord r) =>
         EffTr r ((Entity -> Bool) -> (Entity -> Bool) -> (Entity -> Bool))
or_VP f1 f2 = \x -> do f <- coord (CoordMode Disj Pos) f1 f2
                       f x


runAll = run . (flip runFresh) 0 . makeChoice . runRef [] . ec . runCoord

donkeySentence = beatsSWS it (every (who (ownsSWS (a donkey)) farmer))
donkeySentenceR = runAll donkeySentence

johnBeatsADonkey = beatsSWS (a donkey) john
johnBeatsADonkeyR = runAll johnBeatsADonkey

heBeatsIt = beatsSWS it he
heBeatsItR = runAll heBeatsIt

dsANDhbi = donkeySentence `and'` heBeatsIt
dsANDhbiR = runAll dsANDhbi

jbadANDhbi = johnBeatsADonkey `and'` heBeatsIt
jbadANDhbiR = runAll jbadANDhbi

every_a = beatsSWS (a donkey) (every farmer)
every_aR = runAll every_a

eaANDhbi = every_a `and'` heBeatsIt
eaANDhbiR = runAll eaANDhbi

a_every = beatsOWS (a donkey) (every farmer)
a_everyR = runAll a_every

aeANDhbi = a_every `and'` heBeatsIt
aeANDhbiR = runAll aeANDhbi

slowlySent = slowly (beatsSWS john) (a farmer)
slowlySentR = runAll slowlySent

conjSent = ownsSWS (and_NP john (a donkey)) mary
conjSentR = runAll conjSent

nestedConjSent = ownsSWS (and_NP john mary) (every donkey)
nestedConjSentR = runAll nestedConjSent
