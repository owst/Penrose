-- | builds basic MTBDDs
module MTBDD.Make
    ( constant
    , unitWithVars
    ) where

import MTBDD.Internals

import Control.Monad.Identity ( runIdentity )
import Data.Foldable ( foldrM )

constant :: (Ord v, Ord e) => e -> MTBDD v e
constant = runIdentity . make . register . Leaf

-- Create an MTBDD, from a binary "path" to a value. The variables of the MTBDD
-- are indices in the path. An "empty" value must be provided, taken for the
-- value of the complement of the given paths.
--
-- This path must be ordered by < on the v.
unitWithVars :: (Ord v, Ord e) => e -> [(v, Bool)] -> e -> MTBDD v e
unitWithVars _ [] value = runIdentity . make . register $ Leaf value
unitWithVars empty validPath value = runIdentity . make $ do
    emptyLeaf <- register $ Leaf empty
    val <- register $ Leaf value
    let combine (vid, isR) v
            | isR = register $ Branch vid emptyLeaf v
            | otherwise = register $ Branch vid v emptyLeaf
    foldrM combine val validPath
