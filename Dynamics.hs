{-# OPTIONS -W #-}
{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Dynamics where

-- Philippe de Groote. 2010.  Dynamic logic: a type-theoretic view.
-- Talk slides at `Le modèle et l'algorithme', Rocquencourt.
-- http://www.inria.fr/rocquencourt/rendez-vous/modele-et-algo/dynamic-logic-a-type-theoretic-view

import Semantics
import CFG
import QCFG

-- We extend the Lambda language with state (of the type State)
type State = [Entity]
class (Lambda lrepr) => States lrepr where
  update :: lrepr Entity -> lrepr State -> lrepr State
  select :: lrepr State -> lrepr Entity
  select_:: Int -> lrepr State -> lrepr Entity
  nil    :: lrepr State

-- We correspondingly extend our R, C, P interpreters of Lambda
instance States R where
  update (R x) (R e) = R (x:e)
  select (R [])      = error "who?"
  select (R (x:_))   = R x
  select_ n (R xs)   = R (xs !! n)
  nil                = R []

instance States C where
  update (C x) (C e) = C (\i p -> paren (p > 5) (x i 6 ++ "::" ++ e i 5))
  select (C e)       = C (\i p -> paren (p > 10) ("sel " ++ e i 11))
  select_ n (C e)    = C (\i p -> paren (p > 10) ("sel_" ++ show n ++ " " ++ e i 11))
  nil                = C (\_ _ -> "nil")

type instance Known lrepr [a] = (P lrepr a, P lrepr [a])
instance (States lrepr) => States (P lrepr) where
  update x e                   = P (update (unP x) (unP e)) (Just (x,e))
  select (P e _)               = unknown (select e)
  select_ n (P e Nothing)      = unknown (select_ n e)
  select_ 0 (P _ (Just (x,_))) = x
  select_ n (P _ (Just (_,e))) = select_ (n-1) e
  nil                          = unknown nil

type family Dynamic (a :: *)
type instance Dynamic (a -> b) = Dynamic a -> Dynamic b
type instance Dynamic Entity   = Entity
type instance Dynamic Bool     = State -> (State -> Bool) -> Bool
data D lrepr a = D { unD :: lrepr (Dynamic a) }
instance (States lrepr) => Lambda (D lrepr) where
  app (D f) (D x)  = D (app f x)
  lam f            = D (lam (\x -> unD (f (D x))))
  john'            = D john'
  mary'            = D mary'
  like'            = D (dynamic (\_ -> like'))
  own'             = D (dynamic (\_ -> own'))
  farmer'          = D (dynamic (\_ -> farmer'))
  donkey'          = D (dynamic (\_ -> donkey'))
  green'           = D (dynamic (\_ -> green'))
  true             = D (dynamic (\_ -> true))
  neg (D x)        = D (dynamic (\e -> neg (static x e)))
  conj (D x) (D y) = D (lam (\e -> lam (\phi -> app (app x e)
                       (lam (\e -> app (app y e) phi)))))
  impl x y         = neg (x `conj` (neg y))
  exists           = D (lam (\p -> lam (\e -> lam (\phi -> app exists
                       (lam (\x -> app (app (app p x) (update x e)) phi))))))
  forall           = lam (\p -> neg (app exists
                            (lam (\x -> neg (app p x)))))
  -- forall           = D (lam (\p -> lam (\e -> lam (\phi -> app forall
  --                      (lam (\x -> app (app (app p x) (update x e)) phi))))))
instance Show (Sem (D C) S) where
  show = show . unSem
instance Show (Sem (D (P C)) S) where
  show = show . unSem
instance Show (D C Bool) where
  show (D x) = show x
instance Show (D (P C) Bool) where
  show (D x) = show x
class Predicate a where
  dynamic :: (Lambda lrepr) => (lrepr State -> lrepr a) -> lrepr (Dynamic a)
  static  :: (Lambda lrepr) => lrepr (Dynamic a) -> lrepr State -> lrepr a
instance Predicate Bool where
  dynamic f  = lam (\e -> lam (\phi -> conj (f e) (app phi e)))
  static x e = app (app x e) (lam (\_ -> true))
instance (Predicate a) => Predicate (Entity -> a) where
  dynamic f  = lam (\o -> dynamic (\e -> app (f e) o))
  static x e = lam (\o -> static (app x o) e)

class (Lambda lrepr) => Dynamics lrepr where
  it' :: lrepr ((Entity -> Bool) -> Bool)
  it'_ :: Int -> lrepr ((Entity -> Bool) -> Bool)

instance (States lrepr) => Dynamics (D lrepr) where
  it'    = D (lam (\p -> lam (\e -> lam (\phi ->
              app (app (app p (select e)) e) phi))))
  it'_ n = D (lam (\p -> lam (\e -> lam (\phi ->
              app (app (app p (select_ n e)) e) phi))))

instance Dynamics C where
  it'    = C (\_ _ -> "it")
  it'_ n = C (\_ _ -> "it_" ++ show n)

instance (Dynamics lrepr) => Dynamics (P lrepr) where
  it'    = unknown it'
  it'_ n = unknown (it'_ n)

class (Quantifier repr) => Pronoun repr where
  it_  :: repr QNP
  it__ :: Int -> repr QNP

instance Pronoun EN where
  it_    = EN "it"
  it__ _ = EN "it"

instance (Dynamics lrepr) => Pronoun (Sem lrepr) where
  it_    = Sem it'
  it__ n = Sem (it'_ n)

sen6 = r4 (every (who (r5 own (a donkey)) farmer)) (r5 like it_)
sen6_en   = sen6 :: EN S
sen6_sem  = sen6 :: Sem (D C) S
sen6_semp = sen6 :: Sem (D (P C)) S
{-
Lx1. Lx2. -(E (Lx3. farmer' x3 & 
  E (Lx4. donkey' x4 & own' x4 x3 & -(like' (sel (x4::x3::x1)) x3)))) & x2 x1
-}
{-
Lx1. Lx2. -(E (Lx3. -(-(farmer' x3 & 
  E (Lx4. donkey' x4 & own' x4 x3 & -(like' (sel (x4::x3::x1)) x3)))))) & x2 x1
-}

-- with explicit forall
{-
Lx1. Lx2. A (Lx3. -(farmer' x3 & 
   E (Lx4. donkey' x4 & own' x4 x3 & -(like' (sel (x4::x3::x1)) x3))) & x2 (x3::x1))
-}

sen6_ = r4 (every (who (r5 own (a donkey)) farmer)) (r5 like (it__ 0))
sen6__en   = sen6_ :: EN S
sen6__sem  = sen6_ :: Sem (D C) S
sen6__semp = sen6_ :: Sem (D (P C)) S
