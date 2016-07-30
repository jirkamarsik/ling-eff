
-- Local Variables:
-- idris-packages: ("effects")
-- End:

module Main

import Effect.State


data BTree a = Leaf
             | Node (BTree a) a (BTree a)

instance Show a => Show (BTree a) where
  show Leaf = "[]"
  show (Node l x r) = "[" ++ show l ++ " "
                          ++ show x ++ " "
                          ++ show r ++ "]"

testTree : BTree String
testTree = Node (Node Leaf "Jim" Leaf)
                "Fred"
                (Node (Node Leaf "Alice" Leaf)
                      "Sheila"
                      (Node Leaf "Bob" Leaf))


treeTagAux : BTree a
           -> { ['Tag ::: STATE Int,
                 'Leaves ::: STATE Int] } Eff (BTree (Int, a))
treeTagAux Leaf = do
    'Leaves :- update (+1)
    pure Leaf
treeTagAux (Node l x r) = do
    l' <- treeTagAux l
    i <- 'Tag :- get
    'Tag :- put (i + 1)
    r' <- treeTagAux r
    pure (Node l' (i, x) r')

treeTag : (i : Int) -> BTree a -> (Int, BTree (Int, a))
treeTag i x = runPureInit ['Tag := i, 'Leaves := 0]
                    (do x' <- treeTagAux x
                        leaves <- 'Leaves :- get
                        pure (leaves, x'))

main : IO ()
main = print (treeTag 1 testTree)

stateLength : { [STATE String] } Eff Nat
stateLength = pure (length !get)
