module Fbpmn.Helper where

import Data.Containers.ListUtils (nubOrd)
import Data.Map.Strict (keys, (!?))

mapMap :: Ord a => (a -> Maybe b -> Maybe c) -> Map a b -> [c]
mapMap g m = catMaybes $ mapMapElement g m <$> keys m

mapMapElement :: Ord a => (a -> Maybe b -> Maybe c) -> Map a b -> a -> Maybe c
mapMapElement g m k = g k (m !? k)

filter' :: (Ord a) => [a] -> Map a b -> (Maybe b -> Bool) -> [a]
filter' xs f p = filter p' xs where p' x = p $ f !? x

tlift2 :: (Maybe a, Maybe b) -> Maybe (a, b)
tlift2 (Just x, Just y) = Just (x, y)
tlift2 (_     , _     ) = Nothing

{-|
Checks whether all elements of a list are different.
-}
allDifferent :: (Ord a) => [a] -> Bool
allDifferent xs = length xs == (length . nubOrd $ xs)

{-|
Checks whether two lists are disjoint (no common elements).
-}
disjoint :: (Eq a) => [a] -> [a] -> Bool
disjoint xs ys = not (any (`elem` ys) xs)

{-|
applyFanout version of disjoint.
-}
disjoint' :: (Eq a) => (b -> [a]) -> (b -> [a]) -> b -> Bool
disjoint' = applyFanout disjoint

{-|
Combines the elements of a list with their indexes.
-}
withIndex :: [a] -> [(Natural, a)]
withIndex = f 0
  where
    f _ [] = []
    f n (x : xs) = (n, x) : f (n + 1) xs

{-|
Given two lists, xs and ys,
checks whether xs includes all elements of ys.
-}
includesAll :: (Eq a) => [a] -> [a] -> Bool
includesAll xs = all (`elem` xs)

{-|
applyFanout version of includesAll.
-}
includesAll' :: (Eq a) => (b -> [a]) -> (b -> [a]) -> b -> Bool
includesAll' = applyFanout includesAll

{-|
Given two lists, xs and ys,
checks whether all elements in xs are in ys.
-}
allIn :: (Eq a) => [a] -> [a] -> Bool
allIn = flip includesAll

{-|
applyFanout version of allIn.
-}
allIn' :: (Eq a) => (b -> [a]) -> (b -> [a]) -> b -> Bool
allIn' = applyFanout allIn

{-|
Given
h :: c -> [a],
f :: c -> Map a b, and
x::c,
checks whether every element in f x is a key in map h x.
-}
allKeyIn ::
  (Eq a) =>
  (c -> [a]) ->
  (c -> Map a b) ->
  c ->
  Bool
allKeyIn f g x = ks `includesAll` f x
  where
    ks = keys . g $ x

applyFanout :: (b1 -> b2 -> c) -> (a -> b1) -> (a -> b2) -> a -> c
applyFanout f g h = uncurry f . (g &&& h)
