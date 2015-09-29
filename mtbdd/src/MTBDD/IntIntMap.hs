module MTBDD.IntIntMap
    ( IntIntMap
    , empty
    , lookup
    , insert
    , singleton
    ) where

import Prelude hiding ( lookup )

import Data.IntMap ( IntMap )
import qualified Data.IntMap.Strict as M

newtype IntIntMap v = IntIntMap (IntMap (IntMap v))
                    deriving ( Show, Eq, Ord )

empty :: IntIntMap v
empty = IntIntMap M.empty

singleton :: (Int, Int) -> v -> IntIntMap v
singleton (i, j) v = IntIntMap . M.singleton i $ M.singleton j v

lookup :: (Int, Int) -> IntIntMap v -> Maybe v
lookup (i, j) (IntIntMap mm) = M.lookup i mm >>= M.lookup j

insert :: (Int, Int) -> v -> IntIntMap v -> IntIntMap v
insert (i, j) v (IntIntMap mm) = case M.lookup i mm of
    Nothing -> IntIntMap $ M.insert i (M.singleton j v) mm
    Just m -> IntIntMap $ M.insert i (M.insert j v m) mm

