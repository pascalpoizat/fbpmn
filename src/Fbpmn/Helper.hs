module Fbpmn.Helper where

import           Data.Map.Strict   ((!?), keys)

mapMap :: Ord a => (a -> Maybe b -> Maybe c) -> Map a b -> [c]
mapMap g m = catMaybes $ mapMapElement g m <$> keys m

mapMapElement :: Ord a => (a -> Maybe b -> Maybe c) -> Map a b -> a -> Maybe c
mapMapElement g m k = g k (m !? k)

filter' :: (Ord a) => [a] -> (Map a b) -> (Maybe b -> Bool) -> [a]
filter' xs f p = filter p' xs where p' x = p $ f !? x
