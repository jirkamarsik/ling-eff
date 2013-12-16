{-# LANGUAGE DeriveDataTypeable, DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module LinguisticEffectsFirst where

import Eff
import OpenUnion1
import Data.Typeable
import Control.Monad

type family EffTr r a
type instance EffTr r Bool = Eff r Bool
type instance EffTr r Entity = Eff r Entity
type instance EffTr r (a -> b) = (EffTr r a) -> (EffTr r b)

data AnaphoraTag = He | She | It

data Ref e v = FreshR (e -> v) | FetchR AnaphoraTag (e -> v) | StoreR e (e -> v)
             deriving (Typeable, Functor)

freshR :: (Typeable e, Member (Ref e) r) => Eff r e
freshR = send_req FreshR

fetchR :: (Typeable e, Member (Ref e) r) => AnaphoraTag -> Eff r e
fetchR tag = send_req (FetchR tag)

storeR :: (Typeable e, Member (Ref e) r) => e -> Eff r e
storeR ent = send_req (StoreR ent)

data Gen e v = GenR (e -> v)
               deriving (Typeable, Functor)

gen :: (Typeable e, Member (Gen e) r) => Eff r e
gen = send_req GenR

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

genPrefix :: String -> Int -> Eff (Gen String :> r) a -> Eff r a
genPrefix prefix n m = loop n (admin m) where
  loop n (Val x) = return x
  loop n (E u) = handle_relay u (loop n) (handler n)
  handler n (GenR k) = loop (n + 1) (k $ prefix ++ show n)

test1 = run $ genPrefix "x" 0 $ (do x <- gen
                                    y <- gen
                                    return (x ++ y :: String))

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

type GQ = (Entity -> Bool) -> Bool

john :: (Member (Ref Entity) r) => EffTr r GQ
john = \p -> p $ storeR (Entity "John")      

mary :: (Member (Ref Entity) r) => EffTr r GQ
mary = \p -> p $ storeR (Entity "Mary")

farmer :: EffTr r (Entity -> Bool)
farmer = liftM farmer'

donkey :: EffTr r (Entity -> Bool)
donkey = liftM donkey'

owns :: EffTr r (GQ -> GQ -> Bool)
owns o s = s (\x -> o (\y -> do xv <- x; yv <- y; return $ owns' yv xv))

beats :: EffTr r (GQ -> GQ -> Bool)
beats o s = s (\x -> o (\y -> do xv <- x; yv <- y; return $ beats' yv xv))

it :: (Member (Ref Entity) r) => EffTr r GQ 
it = \p -> p $ fetchR It

he :: (Member (Ref Entity) r) => EffTr r GQ 
he = \p -> p $ fetchR He

she :: (Member (Ref Entity) r) => EffTr r GQ 
she = \p -> p $ fetchR She

who :: EffTr r ((((Entity -> Bool) -> Bool) -> Bool) -> (Entity -> Bool) -> (Entity -> Bool))
who r n x = n x `andM` r (\s -> s x)

a :: (Member (Ref Entity) r) => EffTr r ((Entity -> Bool) -> GQ)
a n s = do x <- freshR
           n (return x) `andM` s (return x)

every :: (Member (Ref Entity) r, Member Choose r) =>
         EffTr r ((Entity -> Bool) -> GQ)
every n s = forall (\x -> notM (runEx' (n x `andM` notM (runEx' (s x)))))


--sent = beats it $ every $ who (owns (a donkey)) farmer
