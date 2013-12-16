{-# LANGUAGE DeriveDataTypeable, DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module LinguisticEffectsAssert where

import Eff
import OpenUnion1
import Data.Typeable
import Control.Monad

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

assertC :: (Member Ref r) => Bool -> 

select :: (Member Choose r) => AnaphoraTag -> [e] -> Eff r e
select tag = choose

top :: (Typeable e, Member Choose r, Member (Gen e) r) =>
       [e] -> Eff (Ref e :> r) a -> Eff r (a, [e])
top rs m = loop rs (admin m) where
  loop rs (Val x) = return (x, rs)
  loop rs (E u) = handle_relay u (loop rs) (handler rs)
  handler rs (FreshR k) = do new_r <- gen
                             loop (new_r : rs) (k new_r)
  handler rs (FetchR tag k) = do selected_r <- select tag rs
                                 loop rs (k selected_r)

enter :: (Typeable e, Member Choose r, Member (Gen e) r, Member (Ref e) r) =>
         [e] -> Eff r a -> Eff r (a, [e])
enter rs m = loop rs (admin m) where
  loop rs (Val x) = return (x, rs)
  loop rs (E u) = interpose u (loop rs) (handler rs)
  handler rs (FreshR k) = do new_r <- gen
                             loop (new_r : rs) (k new_r)
  handler rs (FetchR tag k) = do selected_r <- (select tag rs `mplus'` fetchR tag)
                                 loop rs (k selected_r)

newtype Entity = Entity String deriving (Eq, Typeable)

domain :: [Entity]
domain = [Entity "John", Entity "Mary", Entity "Chiquita"]

exists :: EffTr r ((Entity -> Bool) -> Bool)
exists predM = (liftM or) (mapM (predM . return) domain)

forall :: EffTr r ((Entity -> Bool) -> Bool)
forall predM = (liftM and) (mapM (predM . return) domain)

andM :: EffTr r (Bool -> Bool -> Bool)
andM = liftM2 (&&)

notM :: EffTr r (Bool -> Bool)
notM = liftM not

walks' :: Entity -> Bool
walks' (Entity "John") = True
walks' (Entity _) = False

donkey' :: Entity -> Bool
donkey' (Entity name) = name == "Chiquita"

farmer' :: Entity -> Bool
farmer' (Entity name) = name `elem` ["John", "Mary"]

owns' :: Entity -> Entity -> Bool
owns' (Entity no) (Entity ns) = (ns,no) `elem` [("John","Chiquita"),
                                                ("Mary","Chiquita")]

beats' :: Entity -> Entity -> Bool
beats' (Entity no) (Entity ns) = (ns,no) `elem` [("Mary","John"),
                                                 ("John","Chiquita")]

runEx :: (Member Choose r) => Eff (Ref Entity :> r) Bool -> Eff r Bool
runEx m = loop [] (admin m) where
  loop rs (Val x) = return x
  loop rs (E u) = handle_relay u (loop rs) (handler rs)
  handler rs (FreshR k) = exists (\x -> do xv <- x
                                           loop (xv:rs) (k xv))
  handler rs (FetchR tag k) = do selected_r <- select tag rs
                                 loop rs (k selected_r)
  handler rs (StoreR e k) = loop (e:rs) (k e)

runEx' :: (Member Choose r, Member (Ref Entity) r) =>
          Eff r Bool -> Eff r Bool
runEx' m = loop [] (admin m) where
  loop rs (Val x) = return x
  loop rs (E u) = interpose u (loop rs) (handler rs)
  handler rs (FreshR k) = exists (\x -> do xv <- x
                                           loop (xv:rs) (k xv))
  handler rs (FetchR tag k) = do selected_r <- select tag rs `mplus'` fetchR tag
                                 loop rs (k selected_r)
  handler rs (StoreR e k) = loop (e:rs) (k e)


test2 :: (Member (Ref Entity) r) => Eff r Bool
test2 = do j <- freshR
           return (j == Entity "John") `andM`
             (do h <- fetchR He
                 return (walks' h))

test2r = run $ makeChoice $ runEx $ test2

type Q = (Entity -> Bool) -> Bool

john :: (Member (Ref Entity) r) => EffTr r Q
john = \p -> p $ storeR (Entity "John")      

mary :: (Member (Ref Entity) r) => EffTr r Q
mary = \p -> p $ storeR (Entity "Mary")

farmer :: EffTr r (Entity -> Bool)
farmer = liftM farmer'

donkey :: EffTr r (Entity -> Bool)
donkey = liftM donkey'

owns :: EffTr r (Q -> Q -> Bool)
owns o s = s (\x -> o (\y -> do xv <- x; yv <- y; return $ owns' yv xv))

beats :: EffTr r (Q -> Q -> Bool)
beats o s = s (\x -> o (\y -> do xv <- x; yv <- y; return $ beats' yv xv))

it :: (Member (Ref Entity) r) => EffTr r Q 
it = \p -> p $ fetchR It

he :: (Member (Ref Entity) r) => EffTr r Q 
he = \p -> p $ fetchR He

she :: (Member (Ref Entity) r) => EffTr r Q 
she = \p -> p $ fetchR She

who :: EffTr r ((((Entity -> Bool) -> Bool) -> Bool) -> (Entity -> Bool) -> (Entity -> Bool))
who r n x = n x `andM` r (\s -> s x)

a :: (Member (Ref Entity) r) => EffTr r ((Entity -> Bool) -> Q)
a n s = do x <- freshR
           n (return x) `andM` s (return x)

every :: (Member (Ref Entity) r, Member Choose r) =>
         EffTr r ((Entity -> Bool) -> Q)
every n s = forall (\x -> notM (runEx' (n x `andM` notM (runEx' (s x)))))


--sent = beats it $ every $ who (owns (a donkey)) farmer
