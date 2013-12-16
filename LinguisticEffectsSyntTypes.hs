{-# LANGUAGE DeriveDataTypeable, DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module LinguisticEffectsSyntTypes where

import Eff
import OpenUnion1
import Data.Typeable

import Control.Monad


newtype Entity = Entity String deriving (Eq, Typeable)

data S
data NP
data N

type family EffTr r a
type instance EffTr r S        = Eff r Bool
type instance EffTr r NP       = Eff r Entity
type instance EffTr r N        = Eff r (Entity -> Bool)
type instance EffTr r (a -> b) = (EffTr r a) -> (EffTr r b)


data AnaphoraTag = He | She | It

data Ref v = FreshR (Entity -> v) |
             FetchR AnaphoraTag (Entity -> v) |
             AssertC Bool (() -> v)
             deriving (Typeable, Functor)

freshR :: (Member Ref r) => Eff r Entity
freshR = send_req FreshR

fetchR :: (Member Ref r) => AnaphoraTag -> Eff r Entity
fetchR tag = send_req (FetchR tag)

assertC :: (Member Ref r) => Bool -> Eff r ()
assertC prop = send_req (AssertC prop)


select :: (Member Choose r) => AnaphoraTag -> [e] -> Eff r e
select tag = choose

runRef :: (Member Choose r) => [Entity] -> Eff (Ref :> r) Bool -> Eff r Bool
runRef rs m = loop rs (admin m) where
  loop rs (Val x) = return x
  loop rs (E u) = handle_relay u (loop rs) (handler rs)
  handler rs (FreshR k) = runRef rs $ exists' (\x -> do xv <- x
                                                        loop (xv:rs) (k xv))
  handler rs (FetchR tag k) = do selected_ref <- select tag rs
                                 loop rs (k selected_ref)
  handler rs (AssertC prop k) = fmap (&& prop) $ loop rs (k ())

enter :: (Member Choose r, Member Ref r) => [Entity] -> Eff r Bool -> Eff r Bool
enter rs m = loop rs (admin m) where
  loop rs (Val x) = return x
  loop rs (E u) = interpose u (loop rs) (handler rs)
  handler rs (FreshR k) = exists' (\x -> do xv <- x
                                            loop (xv:rs) (k xv))
  handler rs (FetchR tag k) = do selected_ref <- select tag rs `mplus'` fetchR tag
                                 loop rs (k selected_ref)
  handler rs (AssertC prop k) = fmap (&& prop) $ loop rs (k ())


-- SEMANTICS

domain' :: [Entity]
domain' = [Entity "John", Entity "Mary", Entity "Chiquita"]

exists :: (Entity -> Bool) -> Bool
exists p = any p domain'

exists' :: Eff r (Entity -> Bool) -> Eff r Bool
exists' = liftM exists

forall :: (Entity -> Bool) -> Bool
forall p = all p domain'

forall' :: Eff r (Entity -> Bool) -> Eff r Bool
forall' = liftM forall

and' :: Eff r Bool -> Eff r Bool -> Eff r Bool
and' = liftM2 (&&)

not' :: Eff r Bool -> Eff r Bool
not' = liftM not

eq' :: Eff r Entity -> Eff r Entity -> Eff r Bool
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

john :: (Member Ref r) => EffTr r NP
john = do j <- freshR
          assertC $ j == Entity "John"
          return j

mary :: (Member Ref r) => EffTr r NP
mary = do m <- freshR
          assertC $ m == Entity "Mary"
          return m

farmer :: EffTr r N
farmer = return farmer'

donkey :: EffTr r N
donkey = return donkey'

owns :: EffTr r (NP -> NP -> S)
owns = liftM2 owns'

beats :: EffTr r (NP -> NP -> S)
beats = liftM2 owns'

{-
ownsSWS :: EffTr r (NP -> NP -> S)
ownsSWS = (flip . liftM2 . flip) owns'
-- ownsSWS o s = do sv <- s
--                  ov <- o
--                  return $ owns' ov sv

ownsOWS :: EffTr r (NP -> NP -> S)
ownsOWS = liftM2 owns'
-- ownsOWS o s = do ov <- o
--                  sv <- s
--                  return $ owns' ov sv

beatsSWS :: EffTr r (NP -> NP -> S)
beatsSWS = (flip . liftM2 . flip) beats'

beatsOWS :: EffTr r (NP -> NP -> S)
beatsOWS = liftM2 beats'
-}

it :: (Member Ref r) => EffTr r NP 
it = fetchR It

he :: (Member Ref r) => EffTr r NP 
he = fetchR He

she :: (Member Ref r) => EffTr r NP 
she = fetchR She

who :: EffTr r ((NP -> S) -> N -> N)
who r n = do nv <- n
             n x `and'` r x

a :: (Member Ref r) => EffTr r (N -> NP)
a n = do x <- freshR
         n (return x) >>= assertC
         return x

every :: (Member Ref r, Member Choose r) =>
         EffTr r (N -> (NP -> S) -> S)
every n s = notH (do x <- freshR
                     n (return x) >>= assertC
                     notH (s (return x)))
            where notH = not' . (enter [])


donkeySentence :: (Member Choose r, Member Ref r) => EffTr r S
donkeySentence = every (who (owns (a donkey)) farmer) (beats it)

donkeySentenceR = run $ makeChoice $ runRef [] donkeySentence


runs :: (Eq a) => [a] -> [(Int, a)]
runs []     = []
runs (x:xs) = runs' [(1,x)] xs
              where runs' acc         []     = reverse acc
                    runs' ((n,z):acc) (y:ys) = if y == z then
                                                 runs' ((n+1,z):acc) ys
                                               else
                                                 runs' ((1,y):(n,z):acc) ys
