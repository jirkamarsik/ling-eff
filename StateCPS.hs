{-# LANGUAGE TypeFamilies, UndecidableInstances #-}

module StateCPS where

import Control.Monad


newtype Entity = Entity String
                 deriving (Read, Show, Eq)

data S
data N
data NP

type family Dyn a
type instance Dyn Entity   = Entity
type instance Dyn Bool     = StateCPS [Entity] Bool Bool
type instance Dyn (a -> b) = Dyn a -> Dyn b

type family DynSem a
type instance DynSem S        = Dyn Bool
type instance DynSem N        = Dyn (Entity -> Bool)
type instance DynSem NP       = Dyn ((Entity -> Bool) -> Bool)
type instance DynSem (a -> b) = DynSem a -> DynSem b


-- MONAD

newtype StateCPS s w a = StateCPS {runStateCPS :: s -> (a -> s -> w) -> w}

instance Monad (StateCPS s w) where
  return x = StateCPS $ \e phi -> phi x e
  mv >>= f = StateCPS $ \e phi -> runStateCPS mv e (\v e' -> runStateCPS (f v) e' phi)

runState :: s -> StateCPS s a a -> a
runState e mv = runStateCPS mv e (\x e' -> x)

runCont :: s -> (a -> w) -> StateCPS s w a -> w
runCont e k mv = runStateCPS mv e (\x e' -> k x)


-- EFFECTS

cont :: ((a -> w) -> w) -> StateCPS s w a
cont consumer = StateCPS $ \e phi -> consumer (\x -> phi x e)

fresh :: StateCPS s Bool Entity
fresh = cont exists

get :: StateCPS s w s
get = StateCPS $ \e phi -> phi e e

push :: e -> StateCPS [e] w ()
push x = StateCPS $ \e phi -> phi () (x : e)

select_it :: StateCPS [Entity] w Entity
select_it = StateCPS $ \e phi -> phi (head (filter donkey' e)) e


-- LOGIC

dand :: Dyn (Bool -> Bool -> Bool)
dand = liftM2 (&&)

dnot :: Dyn (Bool -> Bool)
dnot psi = do e <- get
              return (not (runState e psi))

dexists :: Dyn ((Entity -> Bool) -> Bool)
dexists p = p =<< fresh

dimpl :: Dyn (Bool -> Bool -> Bool)
dimpl x y = dnot (x `dand` dnot y)

dforall :: Dyn ((Entity -> Bool) -> Bool)
dforall p = dnot (dexists (\x -> dnot (p x)))


-- SEMANTICS && MODEL

domain :: [Entity]
domain = [Entity "John", Entity "Mary"]

exists :: (Entity -> Bool) -> Bool
exists p = any p domain

farmer' :: Entity -> Bool
farmer' x = x `elem` [Entity "Mary"]

donkey' :: Entity -> Bool
donkey' x = x `elem` [Entity "John"]

own' :: Entity -> Entity -> Bool
own' x y = (x, y) `elem` [(Entity "Mary", Entity "John")]

beat' :: Entity -> Entity -> Bool
beat' = own'


-- SYNTAX - SEMANTICS INTERFACE

farmer :: DynSem N
farmer = \x -> return (farmer' x)

donkey :: DynSem N
donkey = \x -> return (donkey' x)

owns :: DynSem (NP -> NP -> S)
owns = \o s -> s (\x -> o (\y -> return (own' x y)))

beats :: DynSem (NP -> NP -> S)
beats = \o s -> s (\x -> o (\y -> return (beat' x y)))

who :: DynSem ((NP -> S) -> N -> N)
who = \r n x -> n x `dand` r (\psi -> psi x)

a :: DynSem (N -> NP)
a = \n psi -> dexists (\x -> n x `dand` (do push x; psi x))

every :: DynSem (N -> NP)
every = \n psi -> dforall (\x -> n x `dimpl` (do push x; psi x))

it :: DynSem NP
it = \psi -> psi =<< select_it


-- EXAMPLES

donkeySent = beats it (every (who (owns (a donkey)) farmer))
