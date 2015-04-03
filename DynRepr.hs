module DynRepr where

import Data.List
import Data.Maybe

newtype Entity = Entity String
type Context = [Entity]
data Condition = Simple Bool | Neg Box
data Box = Box ((Context -> [Condition]) -> Bool)


man :: Entity -> Bool
man (Entity "John") = True
man _ = False

walks :: Entity -> Bool
walks _ = True

domain :: [Entity]
domain = map Entity ["John", "Mary"]

exists :: (Entity -> Bool) -> Bool
exists p = any p domain

selHe :: Context -> Entity
selHe refs = fromMaybe (Entity "?") (find man refs)

heWalks :: Box -> Box
heWalks (Box f) = Box (\k -> f (\e -> [Simple (walks (selHe e))] ++ k e))

aManWalks :: Box -> Box
aManWalks (Box f) = Box (\k -> exists (\x -> f (\e -> [Simple (walks x)] ++ k (x : e))))
