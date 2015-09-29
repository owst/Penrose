{-# language ScopedTypeVariables, RankNTypes #-}

module MTBDD.Operation
    ( (&&), (||), (**), or
    , binary, binaryM
    , unary, unaryM
    , instantiate, instantiateM
    , onBranchChildren
    , onNodes
      -- Optimised special cases.
    , instantiateAllFalse
    , instantiateAllTrue
    , foldMap
    , binaryFoldMap
    )

where

import MTBDD.Internals
import MTBDD.Make

import Control.Monad.Trans ( lift )
import Control.Parallel.Strategies ( runEval )

import Data.Foldable ( Foldable, foldr )
import Data.Monoid ( Monoid, mappend )
import Data.Set ( Set )
import qualified Data.Set as S

import Prelude hiding ( (&&), (||), (**), or, not, foldr )
import qualified Prelude

-- TODO: generalise to arbitrary Boolean Algebras
type SetBDD v e = MTBDD v (Set e)

(&&) :: (Ord e) => SetBDD v e -> SetBDD v e -> SetBDD v e
x@(MTBDD{}) && y@(MTBDD{}) = binary S.intersection x y

(||) :: (Ord e) => SetBDD v e -> SetBDD v e -> SetBDD v e
x@(MTBDD{}) || y@(MTBDD{}) = binary S.union x y

(**) :: SetBDD v e1 -> SetBDD v e2 -> MTBDD v (Set e1, Set e2)
x@(MTBDD{}) ** y@(MTBDD{}) = binary (,) x y

or :: (Ord v, Ord e, Foldable t) => t (SetBDD v e) -> SetBDD v e
or = foldr (||) (constant S.empty)

infixr 8 .:
(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.:) = (.) . (.)

binary :: (Ord v, Ord e3)
       => (e1 -> e2 -> e3) -> MTBDD v e1 -> MTBDD v e2 -> MTBDD v e3
binary f = runEval .: binaryM (return .: f)

binaryM :: (Monad m, Ord v, Ord e3) => (e1 -> e2 -> BDDMakeT v e3 m e3)
        -> MTBDD v e1 -> MTBDD v e2 -> m (MTBDD v e3)
binaryM op = make . withCache .: handleBinary
  where
    handleBinary x@(MTBDD tx _) y@(MTBDD ty _) = cached (tx, ty) $
        onNodes onLeaves onBranch x y

    -- Lift register through the cache
    liftReg = lift . register

    -- Apply the given operation and then register the resulting Leaf
    onLeaves x y = lift (op x y) >>= (liftReg . Leaf)

    -- After recursing down the appropriate branches, register the resulting
    -- Branch.
    onBranch v = onBranchChildren handleBinary (liftReg .: Branch v)

-- Take two pairs of sub-graphs, and obtain a new Node index from each pair,
-- before combining the indices using the passed function.
onBranchChildren :: (Monad m) => (MTBDD v e1 -> MTBDD v e2 -> m i)
                 -> (i -> i -> m r)
                 -> MTBDD v e1 -> MTBDD v e2 -> MTBDD v e1 -> MTBDD v e2 -> m r
onBranchChildren genIndex withIndices l1 l2 r1 r2 = do
    l' <- genIndex l1 l2
    r' <- genIndex r1 r2
    withIndices l' r'

-- Modify a branch's children, before re-registering
registerBranchChildren :: (Monad m, Ord v, Ord e1, Ord e2)
              => (MTBDD v e1 -> CachedT Index (BDDMakeT v e2 m) Index)
              -> v -> MTBDD v e1 -> MTBDD v e1
              -> CachedT Index (BDDMakeT v e2 m) Index
registerBranchChildren recurse v l r = do
    l' <- recurse l
    r' <- recurse r
    lift . register $ Branch v l' r'

-- Recurse over the structure of a pair of Nodes; on reaching two leaves the
-- leaf function is applied, otherwise the branch function is applied to the
-- appropriate children, preserving the variable order.
onNodes :: (Ord v) => (e1 -> e2 -> m r)
        -> (v -> MTBDD v e1 -> MTBDD v e2 -> MTBDD v e1 -> MTBDD v e2 -> m r)
        -> MTBDD v e1 -> MTBDD v e2 -> m r
onNodes goL goB x y = case (access x, access y) of
    -- Combine the leaves using the passed function
    (Leaf p, Leaf q) -> goL p q
    -- Recurse, passing the leaf down into the branch structure
    (Leaf _, Branch v l r) -> goB v x l x r
    (Branch v l r, Leaf _) -> goB v l y r y
    -- Recurse over the smaller variable, preserving the other branch, unless
    -- the variables are equal, in which case recurse over the pair of
    -- left/right branches simultaneously.
    (Branch v1 l1 r1, Branch v2 l2 r2) -> case compare v1 v2 of
        LT -> goB v1 l1 y r1 y
        GT -> goB v2 x l2 x r2
        EQ -> goB v1 l1 l2 r1 r2

unary :: (Ord v, Ord e2) => (e1 -> e2) -> MTBDD v e1 -> MTBDD v e2
unary f = runEval . unaryM (return . f)

unaryM :: (Monad m, Ord v, Ord e2)
       => (e1 -> m e2) -> MTBDD v e1 -> m (MTBDD v e2)
unaryM op = make . withCache . go
  where
    -- Implement unary caching with binary caching and duplicating the index.
    go x@(MTBDD t _) = cached (t, t) $
        case access x of
            Leaf p -> do
                res <- lift . lift $ op p
                lift . register . Leaf $ res
            Branch v l r -> registerBranchChildren go v l r

instantiateAllFalse :: MTBDD v e -> e
instantiateAllFalse = instantiateAllWith (\x _ -> x)

instantiateAllTrue :: MTBDD v e -> e
instantiateAllTrue = instantiateAllWith (\_ y -> y)

instantiateAllWith :: (MTBDD v e -> MTBDD v e -> MTBDD v e) -> MTBDD v e -> e
instantiateAllWith goLR bdd = case access bdd of
    Leaf p -> p
    Branch _ l r -> instantiateAllFalse (goLR l r)

instantiate :: (Ord v, Ord e) => v -> Bool -> MTBDD v e -> MTBDD v e
instantiate var val = runEval . instantiateM var val

-- | replace variable by value
instantiateM :: (Monad m, Ord v, Ord e)
             => v -> Bool -> MTBDD v e -> m (MTBDD v e)
instantiateM var val = make . withCache . go
  where
    go x@(MTBDD t _) = cached (t, t) $
        case access x of
            Leaf p -> lift . register $ Leaf p
            Branch v l r ->
                if v == var
                    then traverseReregister $ if val then r else l
                    else registerBranchChildren go v l r

    -- The same as 'go', but doesn't need to compare each variable, since we've
    -- already found the variable we care about.
    traverseReregister x@(MTBDD t _) = cached (t, t) $
        case access x of
            Leaf p -> lift . register $ Leaf p
            Branch v l r -> registerBranchChildren traverseReregister v l r

foldMap :: (Monoid m) => (e -> m) -> MTBDD v e -> m
foldMap f = go
  where
    go x = case access x of
        Leaf p -> f p
        Branch _ l r ->
            let lm = go l
                rm = go r
            in lm `mappend` rm

binaryFoldMap :: (Monoid r, Ord v) => (e -> e -> r)
              -> MTBDD v e -> MTBDD v e -> r
binaryFoldMap leaves = runEval .: binaryTraverse lAction bAction
  where
    lAction = return .: leaves
    bAction = const $ return .: mappend

binaryTraverse :: (Monad m, Ord v) => (e1 -> e2 -> m t) -> (v -> t -> t -> m t)
               -> MTBDD v e1 -> MTBDD v e2 -> m t
binaryTraverse leafAction branchAction = onNodes leafAction onBranch
  where
    rec = binaryTraverse leafAction branchAction

    onBranch v = onBranchChildren rec (branchAction v)
