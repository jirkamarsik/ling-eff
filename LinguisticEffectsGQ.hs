{-# LANGUAGE DeriveDataTypeable, DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module LinguisticEffectsGQ where

import Eff
import OpenUnion1
import Data.Typeable

import Control.Monad


newtype Entity = Entity String deriving (Eq, Typeable)

type family EffTr r a
type instance EffTr r Bool = Eff r Bool
type instance EffTr r Entity = Eff r Entity
type instance EffTr r (a -> b) = (EffTr r a) -> (EffTr r b)


data AnaphoraTag = He | She | It

data Ref v = StoreR Entity (() -> v) |
             FetchR AnaphoraTag (Entity -> v)
             deriving (Typeable, Functor)

storeR :: (Member Ref r) => Entity -> Eff r Entity
storeR ref = send_req (StoreR ref)

fetchR :: (Member Ref r) => AnaphoraTag -> Eff r Entity
fetchR tag = send_req (FetchR tag)


select :: (Member Choose r) => AnaphoraTag -> [e] -> Eff r e
select tag = choose

runRef :: (Member Choose r) => [Entity] -> Eff (Ref :> r) Bool -> Eff r Bool
runRef rs m = loop rs (admin m) where
  loop rs (Val x) = return x
  loop rs (E u) = handle_relay u (loop rs) (handler rs)
  handler rs (StoreR ref k) = loop (ref:rs) (k ())
  handler rs (FetchR tag k) = do ref <- select tag rs
                                 loop rs (k ref)

enter :: (Member Choose r, Member Ref r) => [Entity] -> Eff r Bool -> Eff r Bool
enter rs m = loop rs (admin m) where
  loop rs (Val x) = return x
  loop rs (E u) = interpose u (loop rs) (handler rs)
  handler rs (StoreR ref k) = loop (ref:rs) (k ())
  handler rs (FetchR tag k) = do ref <- select tag rs `mplus'` fetchR tag
                                 loop rs (k ref)


-- SEMANTICS

domain' :: [Entity]
domain' = [Entity "John", Entity "Mary", Entity "Chiquita"]

exists' :: EffTr r ((Entity -> Bool) -> Bool)
-- exists' predM = (liftM or) (mapM (predM . return) domain')
exists' predM = (predM . return) (Entity "Chiquita")

forall' :: EffTr r ((Entity -> Bool) -> Bool)
-- forall' predM = (liftM and) (mapM (predM . return) domain')
forall' predM = (predM . return) (Entity "John")

and' :: EffTr r (Bool -> Bool -> Bool)
and' = liftM2 (&&)

not' :: EffTr r (Bool -> Bool)
not' = liftM not

eq' :: EffTr r (Entity -> Entity -> Bool)
eq' = liftM2 (==)

walks' :: Entity -> Bool
walks' (Entity name) = name `elem` ["John"] 

donkey' :: Entity -> Bool
donkey' (Entity name) = name `elem` ["Chiquita"]

farmer' :: Entity -> Bool
farmer' (Entity name) = name `elem` ["John", "Mary"]

owns' :: Entity -> Entity -> Bool
owns' (Entity no) (Entity ns) = (ns,no) `elem` [("John","Chiquita"),
                                                ("Mary","Chiquita")]

beats' :: Entity -> Entity -> Bool
beats' (Entity no) (Entity ns) = (ns,no) `elem` [("Mary","John"),
                                                 ("John","Chiquita")]


-- SYNTAX

type GQ = (Entity -> Bool) -> Bool

john :: (Member Ref r) => EffTr r GQ
john p = do storeR (Entity "John")
            p (return (Entity "John"))

mary :: (Member Ref r) => EffTr r GQ
mary p = do storeR (Entity "Mary")
            p $ return (Entity "Mary")

farmer :: EffTr r (Entity -> Bool)
farmer = liftM farmer'

donkey :: EffTr r (Entity -> Bool)
donkey = liftM donkey'

ownsSWS :: EffTr r (GQ -> GQ -> Bool)
ownsSWS o s = s (\x -> o (\y -> do xv <- x; yv <- y; return $ owns' yv xv))

ownsOWS :: EffTr r (GQ -> GQ -> Bool)
ownsOWS o s = o (\y -> s (\x -> do xv <- x; yv <- y; return $ owns' yv xv))

beatsSWS :: EffTr r (GQ -> GQ -> Bool)
beatsSWS o s = s (\x -> o (\y -> do xv <- x; yv <- y; return $ beats' yv xv))

beatsOWS :: EffTr r (GQ -> GQ -> Bool)
beatsOWS o s = o (\y -> s (\x -> do xv <- x; yv <- y; return $ beats' yv xv))

it :: (Member Ref r) => EffTr r GQ 
it p = do it <- fetchR It
          p $ (return it)

he :: (Member Ref r) => EffTr r GQ 
he p = do he <- fetchR He
          p $ (return he)

she :: (Member Ref r) => EffTr r GQ 
she p = do she <- fetchR She
           p $ (return she)

who :: EffTr r ((GQ -> Bool) -> (Entity -> Bool) -> (Entity -> Bool))
who r n x = n x `and'` r (\s -> s x)

a :: (Member Ref r) => EffTr r ((Entity -> Bool) -> GQ)
a n s = do x <- freshR
           n (return x) `and'` s (return x)

every :: (Member Ref r, Member Choose r) => EffTr r ((Entity -> Bool) -> GQ)
every n s = notH (exists' (\x -> n x `and'` notH (s x)))
            where notH = not' . (enter [])

