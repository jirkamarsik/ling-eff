{-# LANGUAGE DeriveFunctor,
             DeriveFoldable,
             DeriveTraversable,
             PackageImports #-}

module Label where

import "mtl" Control.Monad.State
import Data.Foldable
import Data.Traversable

data Tree a = Branch (Tree a) a (Tree a) | Leaf a
              deriving (Show, Read, Eq, Functor, Foldable, Traversable)


relabel0 :: Tree a -> Tree Int
relabel0 tree = fst (relabel' tree 0) where

  relabel' :: Tree a -> Int -> (Tree Int, Int)
  relabel' (Leaf value)              n = (Leaf n, n + 1)
  relabel' (Branch left value right) n =
    let (newLeft, newValue) = relabel' left n
        (newRight, newN)    = relabel' right (newValue + 1) in
    (Branch newLeft newValue newRight, newN)


relabel1 :: Tree a -> Tree Int
relabel1 tree = fst (relabel' tree 0) where

  relabel' :: Tree a -> Int -> (Tree Int, Int)
  relabel' (Leaf value)              n0 =
    let (newValue, n1) = (n0, n0 + 1) in
        (Leaf newValue, n1)
  relabel' (Branch left value right) n0 =
    let (newLeft,  n1) = relabel' left n0
        (newValue, n2) = (n1, n1 + 1)
        (newRight, n3) = relabel' right n2 in
    (Branch newLeft newValue newRight, n3)


relabel2 :: Tree a -> Tree Int
relabel2 tree = evalState (relabel' tree) 0 where

  relabel' :: Tree a -> State Int (Tree Int)
  relabel' (Leaf value)              =
    do newValue <- relabelNode value
       return (Leaf newValue)
  relabel' (Branch left value right) =
    do newLeft  <- relabel' left
       newValue <- relabelNode value
       newRight <- relabel' right
       return (Branch newLeft newValue newRight)

  relabelNode :: a -> State Int Int
  relabelNode old = do n <- get
                       put (n + 1)
                       return n


relabel3 :: Tree a -> Tree Int
relabel3 tree = evalState (traverse relabelNode tree) 0 where

  relabelNode :: a -> State Int Int
  relabelNode old = do n <- get
                       put (n + 1)
                       return n

