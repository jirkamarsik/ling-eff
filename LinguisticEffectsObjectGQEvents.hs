{-# LANGUAGE DeriveDataTypeable, DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module LinguisticEffectsObjectGQEvents where

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
             FetchR AnaphoraTag (Formula Entity -> v) |
             AssertC (Formula Bool) (() -> v)
             deriving (Typeable, Functor)

freshR :: (Member Ref r) => Eff r (Formula Entity)
freshR = send_req FreshR

fetchR :: (Member Ref r) => AnaphoraTag -> Eff r (Formula Entity)
fetchR tag = send_req (FetchR tag)

assertC :: (Member Ref r) => Formula Bool -> Eff r ()
assertC prop = send_req (AssertC prop)

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
  handler rs (FreshR k) = exists' (\x -> do xv <- x
                                            loop (xv:rs) (k xv))
  handler rs (FetchR tag k) = do selected_ref <- select tag rs
                                 loop rs (k selected_ref)
  handler rs (AssertC prop k) = (return prop) `and'` loop rs (k ())

enter :: (Member Choose r, Member Fresh r, Member Ref r) =>
         Eff r (Formula Bool) -> Eff r (Formula Bool)
enter m = loop [] (admin m) where
  loop rs (Val x) = return x
  loop rs (E u) = interpose u (loop rs) (handler rs)
  handler rs (FreshR k) = exists' (\x -> do xv <- x
                                            loop (xv:rs) (k xv))
  handler rs (FetchR tag k) = do selected_ref <- select tag rs `mplus'` fetchR tag
                                 loop rs (k selected_ref)
  handler rs (AssertC prop k) = (return prop) `and'` loop rs (k ())


ec :: (Member Fresh r) =>
               Eff (Event :> r) (Formula Bool) -> Eff r (Formula Bool)
ec m = do n <- fresh
          let var = Sym ("e" ++ show n)
              loop (Val x) = return $ App (Var (Sym "exists")) (Abs var x) 
              loop (E u) = handle_relay u loop handler
              handler (EventR k) = loop (k (Var var))
          loop (admin m) where


scopeDomain :: (Member Fresh r, Member Event r) =>
               Eff r (Formula Bool) -> Eff r (Formula Bool)
scopeDomain m = do n <- fresh
                   let var = Sym ("e" ++ show n)
                       loop (Val x) = return $ App (Var (Sym "exists")) (Abs var x) 
                       loop (E u) = interpose u loop handler
                       handler (EventR k) = loop (k (Var var))
                   loop (admin m) where


-- SEMANTICS

fill :: (Member Fresh r) =>
        (Eff r (Formula a) -> Eff r (Formula b)) -> Eff r (Formula (a -> b))
fill f = do n <- fresh
            let var = Sym ("x" ++ show n)
            body <- f (return (Var var))
            return (Abs var body)

exists' :: (Member Fresh r) => EffTr r ((Entity -> Bool) -> Bool)
exists' p = fmap (App (Var (Sym "exists"))) (fill p)

forall' :: (Member Fresh r) => EffTr r ((Entity -> Bool) -> Bool)
forall' p = fmap (App (Var (Sym "forall"))) (fill p)

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

andF :: Formula Bool -> Formula Bool -> Formula Bool
andF = liftF2 (Sym "and")

and' :: EffTr r (Bool -> Bool -> Bool)
and' = liftM2 andF

notF :: Formula Bool -> Formula Bool
notF = liftF (Sym "not")

not' :: EffTr r (Bool -> Bool)
not' = liftM notF

eqF :: Formula Entity -> Formula Entity -> Formula Bool
eqF = liftF2 (Sym "=")

eq' :: EffTr r (Entity -> Entity -> Bool)
eq' = liftM2 eqF


-- SYNTAX

type GQ = (Entity -> Bool) -> Bool

john :: (Member Ref r) => EffTr r Entity
john = do j <- freshR
          assertC $ j `eqF` Var (Sym "john")
          return j

mary :: (Member Ref r) => EffTr r Entity
mary = do m <- freshR
          assertC $ m `eqF` Var (Sym "mary")
          return m

farmer :: EffTr r (Entity -> Bool)
farmer = liftFM (Sym "farmer")

donkey :: EffTr r (Entity -> Bool)
donkey = liftFM (Sym "donkey")

owns :: (Member Event r) => EffTr r (Entity -> Entity -> Bool)
owns = liftFM3 (Sym "owns") eventR

beats :: (Member Event r) => EffTr r (Entity -> Entity -> Bool)
beats = liftFM3 (Sym "beats") eventR

slowly :: (Member Event r) => EffTr r ((Entity -> Bool) -> (Entity -> Bool))
slowly p x = liftFM (Sym "slow") eventR `and'` p x

it :: (Member Ref r) => EffTr r Entity 
it = fetchR It

he :: (Member Ref r) => EffTr r Entity 
he = fetchR He

she :: (Member Ref r) => EffTr r Entity 
she = fetchR She

who :: (Member Event r, Member Fresh r) =>
       EffTr r ((Entity -> Bool) -> (Entity -> Bool) -> (Entity -> Bool))
who r n x = n x `and'` (scopeDomain (r x))

a :: (Member Ref r) => EffTr r ((Entity -> Bool) -> GQ)
a n s = do x <- freshR
           n (return x) >>= assertC
           s (return x)

every :: (Member Ref r, Member Choose r, Member Fresh r, Member Event r) =>
         EffTr r ((Entity -> Bool) -> GQ)
every n s = notH (do x <- freshR
                     n (return x) >>= assertC
                     notH (scopeDomain (s (return x))))
            where notH = not' . enter


runAll = run . (flip runFresh) 0 . makeChoice . runRef [] . ec

donkeySentence = every (who (\x -> (a donkey) (\y -> owns y x)) farmer) (beats it)
donkeySentenceR = runAll donkeySentence

johnBeatsADonkey = a donkey (\x -> beats x john)
johnBeatsADonkeyR = runAll johnBeatsADonkey

heBeatsIt = beats it he
heBeatsItR = runAll heBeatsIt

dsANDhbi = donkeySentence `and'` heBeatsIt
dsANDhbiR = runAll dsANDhbi

jbadANDhbi = johnBeatsADonkey `and'` heBeatsIt
jbadANDhbiR = runAll jbadANDhbi

every_a = every farmer (\x -> (a donkey) (\y -> (beats y x)))
every_aR = runAll every_a

eaANDhbi = every_a `and'` heBeatsIt
eaANDhbiR = runAll eaANDhbi

a_every = a donkey (\y -> (every farmer) (\x -> (beats y x)))
a_everyR = runAll a_every

aeANDhbi = a_every `and'` heBeatsIt
aeANDhbiR = runAll aeANDhbi

slowlySent = a farmer (slowly (beats john))
slowlySentR = runAll slowlySent
