{-# LANGUAGE TypeFamilies #-}

module Alizations where

import Semantics
import Dynamics

newtype World = World Int

type family Intens a
type instance Intens Entity = World -> Entity
type instance Intens Bool = World -> Bool
type instance Intens (a -> b) = Intens a -> Intens b

type instance Dynamic World = World

class Dynamize a where
  dynamize :: (States lrepr) => (lrepr State -> lrepr a) -> lrepr (Dynamic a)
  statize  :: (States lrepr) => lrepr (Dynamic a) -> lrepr State -> lrepr a
instance Dynamize Bool where
  dynamize p  = lam (\e -> lam (\phi -> conj (p e) (app phi e)))
  statize p e = app (app p e) (lam (\_ -> true))
instance Dynamize Entity where
  dynamize a  = a nil
  statize a e = a
instance Dynamize World where
  dynamize a  = a nil
  statize a e = a
instance (Dynamize a, Dynamize b) => Dynamize (a -> b) where
  dynamize f  = lam (\a -> dynamize (\e -> app (f e) (statize a e)))
  statize f e = lam (\a -> statize (app f (dynamize (\e -> a))) e)


class (Lambda lrepr) => Fake lrepr where
  student' :: lrepr (Intens (Entity -> Bool))
  fake' :: lrepr (Intens ((Entity -> Bool) -> (Entity -> Bool)))

instance Fake C where
  student' = C (\_ _ -> "student'")
  fake' = C (\_ _ -> "fake'")

instance (Fake lrepr) => Fake (P lrepr) where
  student' = unknown student'
  fake' = unknown fake'


dynamicDonkey :: P C (Dynamic (Entity -> Bool))
dynamicDonkey = dynamize (\_ -> donkey')

dynamicFake :: P C (Dynamic (Intens ((Entity -> Bool) -> (Entity -> Bool))))
dynamicFake = dynamize (\_ -> fake')
