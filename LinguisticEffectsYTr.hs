{-# LANGUAGE DeriveDataTypeable, DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module LinguisticEffectsYTr where

import Eff
import OpenUnion1
import Data.Typeable

import Semantics

data NP
data N
data S

class Sym repr where
  john   :: repr NP
  mary   :: repr NP
  he     :: repr NP
  she    :: repr NP
  it     :: repr NP
  farmer :: repr N
  donkey :: repr N
  owns   :: repr (NP -> NP -> S)
  beats  :: repr (NP -> NP -> S)
  likes  :: repr (NP -> NP -> S)
  who    :: repr ((NP -> S) -> N -> N)
  a      :: repr (N -> NP)
  every  :: repr (N -> NP)
  lamS   :: (repr a -> repr b) -> repr (a -> b)
  appS   :: repr (a -> b) -> repr a -> repr b
 

type family SemTr a
type instance SemTr NP       = Entity
type instance SemTr N        = Entity -> Bool
type instance SemTr S        = Bool
type instance SemTr (a -> b) = SemTr a -> SemTr b

type family EffTr r a
type instance EffTr r Bool     = Eff r Bool
type instance EffTr r Entity   = Eff r Entity
type instance EffTr r (a -> b) = (EffTr r a) -> (EffTr r b)

type family XTr r a
type instance XTr r Bool     = Bool
type instance XTr r Entity   = Entity
type instance XTr r (a -> b) = (Eff r (XTr r a)) -> (Eff r (XTr r b))

type YTr r a = Eff r (XTr r a)

newtype Sem lrepr r a = Sem {unSem :: EffTr r (lrepr (SemTr a))}


data AnaphoraTag = He | She | It

data Ref lrepr v = FreshR (lrepr Entity -> v) |
                   FetchR AnaphoraTag (lrepr Entity -> v) |
                   AssertC (lrepr Bool) (() -> v)
                   deriving Functor

freshR :: (Typeable1 (Ref lrepr), Member (Ref lrepr) r) =>
          Eff r (lrepr Entity)
freshR = send_req FreshR

fetchR :: (Typeable1 (Ref lrepr), Member (Ref lrepr) r) =>
          AnaphoraTag -> Eff r (lrepr Entity)
fetchR tag = send_req (FetchR tag)

assertC :: (Typeable1 (Ref lrepr), Member (Ref lrepr) r) =>
           lrepr Bool -> Eff r ()
assertC prop = send_req (AssertC prop)

select :: (Member Choose r) => AnaphoraTag -> [e] -> Eff r e
select tag = choose

runEx :: (Typeable1 (Ref lrepr), Lambda lrepr, Member Choose r) =>
         Eff (Ref lrepr :> r) (lrepr Bool) -> Eff r (lrepr Bool)
runEx m = loop [] (admin m) where
  loop rs (Val x) = return x
  loop rs (E u) = handle_relay u (loop rs) (handler rs)
  --handler rs (FreshR k) = app exists (lam (\x -> loop (x:rs) (k x)))
  handler rs (FetchR tag k) = do selected_r <- select tag rs
                                 loop rs (k selected_r)
  handler rs (AssertC prop k) = fmap (conj prop) $ loop rs $ k ()

runEx' :: (Typeable1 (Ref lrepr), Lambda lrepr, Member Choose r, Member (Ref lrepr) r) => Eff r (lrepr Bool) -> Eff r (lrepr Bool)
runEx' m = loop [] (admin m) where
  loop rs (Val x) = return x
  loop rs (E u) = interpose u (loop rs) (handler rs)
  --handler rs (FreshR k) = exists (\x -> do xv <- x
  --                                         loop (xv:rs) (k xv))
  handler rs (FetchR tag k) = do selected_r <- select tag rs `mplus'` fetchR tag
                                 loop rs (k selected_r)
  handler rs (AssertC prop k) = fmap (conj prop) $ loop rs $ k ()


newtype EffL lrepr r a = EffL {unEffL :: YTr r (lrepr a)}

instance (Lambda lrepr, Typeable1 (Ref lrepr), Member (Ref lrepr) r) =>
         Lambda (EffL lrepr r) where
  john' = EffL $ do j <- freshR; assertC (eq j john'); return j

instance (Lambda lrepr) => Sym (Sem lrepr r) where
