{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

module LingEff where

import Control.Effects.Eff
import Control.Effects.Search
import Control.Effects.State

c :: (Member (State Int) r, Member (Search Int) r) => Eff r Int
c = do put (3 :: Int)
       x <- choose [1, 2]
       y <- get
       return $ x + y

c' :: Eff '[State Int, Search Int] Int
c' = c

c'' :: Eff '[Search Int, State Int] Int
c'' = c

handleState :: Typeable s => s -> Eff (State s ': r) a -> Eff r a
handleState s c = handle stateHandler c >>= (\f -> f s)

handleChoice :: Typeable s => Eff (Search s ': r) a -> Eff r [a]
handleChoice = handle handleDFS
