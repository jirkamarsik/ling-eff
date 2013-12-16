{-# LANGUAGE DeriveDataTypeable, DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module LinguisticEffectsPlain where

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

exists' :: (Member Choose r, Member Ref r) => EffTr r ((Entity -> Bool) -> Bool)
exists' predM = (liftM or) (mapM (enter [] . predM . return) domain')

forall' :: (Member Choose r, Member Ref r) => EffTr r ((Entity -> Bool) -> Bool)
forall' predM = (liftM and) (mapM (enter [] . predM . return) domain')

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

john :: (Member Ref r) => EffTr r Entity
john = do j <- freshR
          assertC $ j == Entity "John"
          return j

mary :: (Member Ref r) => EffTr r Entity
mary = do m <- freshR
          assertC $ m == Entity "Mary"
          return m

farmer :: EffTr r (Entity -> Bool)
farmer = liftM farmer'

donkey :: EffTr r (Entity -> Bool)
donkey = liftM donkey'

owns :: EffTr r (Entity -> Entity -> Bool)
owns = liftM2 owns'

beats :: EffTr r (Entity -> Entity -> Bool)
beats = liftM2 owns'

{-
ownsSWS :: EffTr r (Entity -> Entity -> Bool)
ownsSWS = (flip . liftM2 . flip) owns'
-- ownsSWS o s = do sv <- s
--                  ov <- o
--                  return $ owns' ov sv

ownsOWS :: EffTr r (Entity -> Entity -> Bool)
ownsOWS = liftM2 owns'
-- ownsOWS o s = do ov <- o
--                  sv <- s
--                  return $ owns' ov sv

beatsSWS :: EffTr r (Entity -> Entity -> Bool)
beatsSWS = (flip . liftM2 . flip) beats'

beatsOWS :: EffTr r (Entity -> Entity -> Bool)
beatsOWS = liftM2 beats'
-}

it :: (Member Ref r) => EffTr r Entity 
it = fetchR It

he :: (Member Ref r) => EffTr r Entity 
he = fetchR He

she :: (Member Ref r) => EffTr r Entity 
she = fetchR She

who :: EffTr r ((Entity -> Bool) -> (Entity -> Bool) -> (Entity -> Bool))
who r n x = n x `and'` r x

a :: (Member Ref r) => EffTr r ((Entity -> Bool) -> Entity)
a n = do x <- freshR
         n (return x) >>= assertC
         return x

every :: (Member Ref r, Member Choose r) =>
         EffTr r ((Entity -> Bool) -> (Entity -> Bool) -> Bool)
every n s = notH (do x <- freshR
                     n (return x) >>= assertC
                     notH (s (return x)))
            where notH = not' . (enter [])


donkeySentence :: (Member Choose r, Member Ref r) => Eff r Bool
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
