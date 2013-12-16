{-# LANGUAGE DeriveDataTypeable, DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module LinguisticEffectsExtInt where

import Eff
import OpenUnion1
import Data.Typeable
import Control.Monad

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


newtype Sem r a = Sem {unSem :: EffTr r (SemTr a)}

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

runEx :: (Member Choose r) => Eff (Ref :> r) Bool -> Eff r Bool
runEx m = loop [] (admin m) where
  loop rs (Val x) = return x
  loop rs (E u) = handle_relay u (loop rs) (handler rs)
  --handler rs (FreshR k) = app exists (lam (\x -> loop (x:rs) (k x)))
  handler rs (FetchR tag k) = do selected_r <- select tag rs
                                 loop rs (k selected_r)
  handler rs (AssertC prop k) = fmap (&& prop) $ loop rs $ k ()

runEx' :: (Member Choose r, Member Ref r) => Eff r Bool -> Eff r Bool
runEx' m = loop [] (admin m) where
  loop rs (Val x) = return x
  loop rs (E u) = interpose u (loop rs) (handler rs)
--   handler rs (FreshR k) = exists (\x -> do xv <- x
--                                           loop (xv:rs) (k xv))
  handler rs (FetchR tag k) = do selected_r <- select tag rs `mplus'` fetchR tag
                                 loop rs (k selected_r)
  handler rs (AssertC prop k) = fmap (&& prop) $ loop rs $ k ()


instance Sym (Sem r) where


newtype EffL r a = EffL {unEffL :: EffTr r a}

instance Lambda (EffL r) where
  john' = EffL $ return $ unR john'
  mary' = EffL $ return $ unR mary'
  farmer' = EffL $ liftM $ unR farmer'
  donkey' = EffL $ liftM $ unR donkey'
  --own'  = EffL $ \o s -> (do sv <- s; ov <- o; return $ (unR own') ov sv)
  own'  = EffL $ liftM2 $ unR own'
  beat' = EffL $ liftM2 $ unR beat'
  like' = EffL $ liftM2 $ unR like'
  true = EffL $ return $ unR true
  neg = EffL . fmap (unR . neg . R) . unEffL
  conj x y = EffL $ do xv <- unEffL x; yv <- unEffL y; return $ unR $ conj (R xv) (R yv)
  impl x y = EffL $ do xv <- unEffL x; yv <- unEffL y; return $ unR $ impl (R xv) (R yv)
  eq x y = EffL $ do xv <- unEffL x; yv <- unEffL y; return $ unR $ eq (R xv) (R yv)
  exists = EffL $ \f -> (liftM or) $ mapM (f . return) domain
  --exists                 = R (\f -> any f domain)  (LIFT THIS!)
  forall = EffL $ \f -> (liftM and) $ mapM (f . return) domain
  --forall                 = R (\f -> all f domain)  (LIFT THIS!)
  iota = EffL $ \f -> (liftM head) $ filterM (f . return) domain 
  --iota                   = R (\f -> let [x] = filter f domain in x)

  app (EffL f) (EffL x) = EffL $ f x
  --lam f = EffL (\x -> return )
{-
  lam f                  = R (\x -> unR (f (R x)))
-}


