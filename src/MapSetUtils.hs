module MapSetUtils where

import Control.Arrow ( (&&&) )
import Data.Set ( Set )
import qualified Data.Set as S ( toList, empty, insert, union, unions, map
                               , foldr, null, deleteFindMin, fromList
                               , intersection, toAscList, fromDistinctAscList
                               , filter )
import Data.Map.Strict ( Map )
import qualified Data.Map.Lazy as M ( size, (!), fromAscList, foldr )
import Data.Maybe ( catMaybes )
import Prelude hiding ( foldl )

emptyIntersection :: (Ord a) => Set a -> Set a -> Bool
emptyIntersection s1 s2 = S.null $ s1 `S.intersection` s2

setContainingEmptySet :: (Ord a) => Set (Set a)
setContainingEmptySet = S.empty `S.insert` S.empty

-- | 'catSetMaybes' removes all the 'Just' elements from a Set of Maybes.
catSetMaybes :: (Ord a) => Set (Maybe a) -> Set a
catSetMaybes = S.fromList . catMaybes . S.toList

-- TODO: use the functions from Data.Foldable instead of these...


-- | andS takes a 'Set Bool' and returns the conjunction of the values within.
andS :: Set Bool -> Bool
andS = S.foldr (&&) True

anySet :: (Ord a) => (a -> Bool) -> Set a -> Bool
anySet f = S.foldr (\x r -> r || f x) False

allSet :: (Ord a) => (a -> Bool) -> Set a -> Bool
allSet f = S.foldr (\x b -> b && f x) True

allMap :: (v -> Bool) -> Map k v -> Bool
allMap f = M.foldr (\x b -> b && f x) True

-- | Construct the powerset of a 'Set'.
powerSet :: (Ord a) => Set a -> Set (Set a)
powerSet xs
    | S.null xs = setContainingEmptySet
    | otherwise = let (x, xs') = S.deleteFindMin xs
                      powerXs = powerSet xs'
                  in powerXs `S.union` S.map (x `S.insert`) powerXs

joinSet :: (Ord b) => (a -> Set b) -> Set a -> Set b
joinSet f = bigUnion . S.map f

bigUnion :: (Ord a) => Set (Set a) -> Set a
bigUnion = S.unions . S.toList

crossSet :: (Ord a, Ord b) => Set a -> Set b -> Set (a, b)
crossSet as bs =
    S.fromDistinctAscList [ (a, b) | a <- S.toAscList as, b <- S.toAscList bs ]

genericMapSize :: (Num a) => Map x y -> a
genericMapSize = fromIntegral . M.size

renumberSet :: (Ord a) => Set a -> a -> Int
renumberSet set = (M.fromAscList numbered M.!)
  where
    numbered = zip (S.toAscList set) [0..]

numberSet :: (Ord a) => Set a -> (Map a Int, Map Int a)
numberSet set =
    (M.fromAscList numberedElems, M.fromAscList $ swap numberedElems)
  where
    swap = map (\(x, y) -> (y, x))
    numberedElems = zip (S.toAscList set) [0..]

-- Filter members of a set by first modifying the elements.
filterOn :: (Ord a, Ord b) => (a -> b) -> (b -> Bool) -> Set a -> Set a
filterOn f want = S.map fst . S.filter (want . snd) . S.map (id &&& f)
