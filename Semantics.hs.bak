{-# OPTIONS -W #-}
{-# LANGUAGE TypeFamilies, FlexibleContexts, NoMonomorphismRestriction #-}

module Semantics where

-- Here we encode the ``target language'', the language
-- to express denotations (or, meanings)
-- Following Montague, our language for denotations
-- is essentially Church's ``Simple Theory of Types''
-- also known as simply-typed lambda-calculus
-- It is a form of a higher-order predicate logic.

data Entity = John | Mary | Chiquita
  deriving (Eq, Show)

-- We define the grammar of the target language the same way
-- we have defined the grammar for (source) fragment

class Lambda lrepr where
  john'  :: lrepr Entity
  mary'  :: lrepr Entity
  farmer':: lrepr (Entity -> Bool)
  donkey':: lrepr (Entity -> Bool)
  own'   :: lrepr (Entity -> Entity -> Bool)
  beat'  :: lrepr (Entity -> Entity -> Bool)
  like'  :: lrepr (Entity -> Entity -> Bool)

  true   :: lrepr Bool
  neg    :: lrepr Bool -> lrepr Bool
  conj   :: lrepr Bool -> lrepr Bool -> lrepr Bool
  impl   :: lrepr Bool -> lrepr Bool -> lrepr Bool
  eq     :: lrepr Entity -> lrepr Entity -> lrepr Bool
  exists :: lrepr ((Entity -> Bool) -> Bool)
  forall :: lrepr ((Entity -> Bool) -> Bool)
  iota   :: lrepr ((Entity -> Bool) -> Entity) -- simplistic definites

  app    :: lrepr (a -> b) -> lrepr a -> lrepr b
  lam    :: (lrepr a -> lrepr b) -> lrepr (a -> b)

-- Examples
lsen1 = neg (conj (neg (neg true)) (neg true))
lsen2 = lam (\x -> neg x) 
lsen3 = app (lam (\x -> neg x)) true

disj x y = neg (conj (neg x) (neg y))
-- disj true (neg true)
ldisj = lam (\x -> lam (\y -> disj x y))
lsen4  = disj true (neg true)
lsen4' = app (app ldisj true) (neg true)

lsene = app exists (lam (\x -> app (app like' mary') x))


-- ``Syntactic sugar''
exists_ r = lam (\p -> app exists (lam (\x -> conj (app r x) (app p x))))
forall_ r = lam (\p -> app forall (lam (\x -> impl (app r x) (app p x))))
false  = neg true


lsenf = app forall (lam (\x -> app (app like' mary') x))


-- The first interpretation: evaluating in the world with John, Mary,
-- and Bool as truth values.
-- Lambda functions are interpreted as Haskell functions and Lambda
-- applications are interpreted as Haskell applications.
-- The interpreter R is metacircular (and so, efficient).

data R a = R { unR :: a }
instance Lambda R where
  john'                  = R John
  mary'                  = R Mary
  own'                   = R (\o s -> elem (s,o) [(John,Chiquita)])
  beat'                  = R (\o s -> elem (s,o) [(John,Chiquita), (Mary,John)])
  like'                  = R (\o s -> elem (s,o) [(John,Mary), (Mary,John)])
  farmer'                = R (\s -> elem s [Mary, John])
  donkey'                = R (\s -> s == Chiquita)

  true                   = R True
  neg (R True)           = R False
  neg (R False)          = R True
  conj (R True) (R True) = R True
  conj _        _        = R False
  impl (R False) _       = R True
  impl _         x       = x
  eq   (R x)     (R y)   = R $ x == y
  exists                 = R (\f -> any f domain)
  forall                 = R (\f -> all f domain)
  iota                   = R (\f -> let [x] = filter f domain in x)

  app (R f) (R x)        = R (f x)
  lam f                  = R (\x -> unR (f (R x)))


domain = [John, Mary, Chiquita]

instance (Show a) => Show (R a) where
  show (R x) = show x


-- ``Running'' the examples
lsen1_r = lsen1 :: R Bool
lsen2_r = lsen2 :: R (Bool -> Bool)
lsen3_r = lsen3 :: R Bool

ldisj_r  = ldisj  :: R (Bool -> Bool -> Bool)

lsen4_r  = lsen4  :: R Bool
lsen4'_r = lsen4' :: R Bool

lsene_r = lsene   :: R Bool
lsenf_r = lsenf   :: R Bool

-- We now interpret Lambda terms as Strings, so we can show
-- our formulas.
-- Actually, not quite strings: we need a bit of _context_:
-- the precedence and the number of variables already bound in the context.
-- The latter number lets us generate unique variable names.

data C a = C { unC :: Int -> Int -> String }
instance Lambda C where
  john'            = C (\_ _ -> "john'")
  mary'            = C (\_ _ -> "mary'")
  own'             = C (\_ _ -> "own'")
  beat'             = C (\_ _ -> "beat'")
  like'            = C (\_ _ -> "like'")
  farmer'          = C (\_ _ -> "farmer'")
  donkey'          = C (\_ _ -> "donkey'")

  true             = C (\_ _ -> "T")
  neg (C x)        = C (\i p -> paren (p > 10) ("-" ++ x i 11))
  conj (C x) (C y) = C (\i p -> paren (p > 3) (x i 4 ++ " & " ++ y i 3))
  impl (C x) (C y) = C (\i p -> paren (p > 2) (x i 3 ++ " => " ++ y i 2))
  eq   (C x) (C y) = C (\i p -> paren (p > 4) (x i 5 ++ " = " ++ y i 5))
  exists           = C (\_ _ -> "E")
  forall           = C (\_ _ -> "A")
  iota             = C (\_ _ -> "I")

  app (C f) (C x)  = C (\i p -> paren (p > 10) (f i 10 ++ " " ++ x i 11))
  lam f            = C (\i p -> let x    = "x" ++ show i
                                    body = unC (f (C (\_ _ -> x))) (i + 1) 0
                                in paren (p > 0) ("L" ++ x ++ ". " ++ body))

instance Show (C a) where
  show (C x) = x 1 0
paren True  text = "(" ++ text ++ ")"
paren False text = text

-- We can now see the examples

lsen1_c = lsen1 :: C Bool
lsen2_c = lsen2 :: C (Bool -> Bool)
lsen3_c = lsen3 :: C Bool

ldisj_c  = ldisj  :: C (Bool -> Bool -> Bool)

-- The displayed difference between lsen4 and lsen4'
-- shows that beta-redices have been reduced. NBE.
lsen4_c  = lsen4  :: C Bool
lsen4'_c = lsen4' :: C Bool

lsene_c = lsene   :: C Bool
lsenf_c = lsenf   :: C Bool


-- Normalizing the terms: performing the apparent redices

type family Known (lrepr :: * -> *) (a :: *)
type instance Known lrepr (a -> b) = P lrepr a -> P lrepr b
type instance Known lrepr Bool     = Bool
data P lrepr a = P { unP :: lrepr a, known :: Maybe (Known lrepr a) }

instance (Lambda lrepr) => Lambda (P lrepr) where
  john'                      = unknown john'
  mary'                      = unknown mary'
  own'                       = unknown own'
  beat'                      = unknown beat'
  like'                      = unknown like'
  farmer'                    = unknown farmer'
  donkey'                    = unknown donkey'

  true                       = P true (Just True)
  neg (P _ (Just False))     = true
  neg (P _ (Just True))      = P (neg true) (Just False)
  neg (P x _)                = unknown (neg x)

  conj x (P _ (Just True))   = x
  conj (P _ (Just True))  y  = y
  conj (P _ (Just False)) _  = false
  conj _ (P _ (Just False))  = false
  conj (P x _) (P y _)       = unknown (conj x y)
  impl (P _ (Just False)) _  = true
  impl (P _ (Just True)) x   = x
  impl (P x _) (P y _)       = unknown (impl x y)
  eq   (P x _) (P y _)       = unknown (eq x y)
  exists                     = unknown exists
  forall                     = unknown forall
  iota                       = unknown iota

  app (P _ (Just f)) x       = f x
  app (P f Nothing ) (P x _) = unknown (app f x)
  lam f                      = P (lam (\x -> unP (f (unknown x)))) (Just f)


instance (Show (lrepr a)) => Show (P lrepr a) where
  show (P x _) = show x
unknown x = P x Nothing

-- Now we can see beautified terms

lsen1_pc = lsen1 :: (P C) Bool
lsen2_pc = lsen2 :: (P C) (Bool -> Bool)
lsen3_pc = lsen3 :: (P C) Bool

ldisj_pc  = ldisj  :: (P C) (Bool -> Bool -> Bool)

-- There is no longer difference between lsen4 and lsen4'
lsen4_pc  = lsen4  :: (P C) Bool
lsen4'_pc = lsen4' :: (P C) Bool

lsene_pc = lsene   :: (P C) Bool
lsenf_pc = lsenf   :: (P C) Bool
