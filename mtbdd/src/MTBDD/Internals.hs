{-# Language StandaloneDeriving, GADTs #-}

-- | implementation of reduced ordered binary decision diagrams.
module MTBDD.Internals
    ( -- * the data type
      MTBDD(..)
    , MTBDDCreateState
    , BDDMakeT
    , Index
    , size
    , values
    -- * for internal use
    , Node (..)
    , make
    , register
    , cached, OpCache
    , CachedT
    , withCache
    , access
    , toDot
    , getPaths
    , vars
    -- * Unsafe utilities for changing internal data
    , unsafeRevar
    , unsafeRevarM
    , unsafeRename
    ) where

import Control.Arrow ( first )
import Control.DeepSeq ( NFData(..) )
import Control.Parallel.Strategies ( runEval )
import Data.Foldable ( foldMap )
import Data.IntMap.Strict ( IntMap )
import Data.List ( intercalate )
import Data.Traversable ( mapM )
import qualified Data.IntMap.Strict as IM

import MTBDD.IntIntMap (IntIntMap)
import qualified MTBDD.IntIntMap as IIM

import Data.Map.Strict ( Map )
import qualified Data.Map.Strict as M

import Data.Set ( Set )
import qualified Data.Set as S

import Control.Monad.Trans.State.Strict ( get, modify, StateT, evalStateT
                                        , runStateT, put )

import Prelude hiding ( null, mapM )
import qualified Prelude

type Index = Int

-- A Node in the MTBDD graph, with variables @v@, leaves @e@ and branch
-- pointers @i@.
data Node v e i = Leaf !e
                | Branch !v !i !i
                deriving ( Eq, Ord, Show )

instance (NFData e) => NFData (Node v e i) where
    rnf (Leaf s) = rnf s
    rnf (Branch v l r) = v `seq` l `seq` r `seq` ()

-- The core data of a MTBDD is the node map - the BDD's graph structure; and,
-- as an optimisation, the set of values that appear in the BDD.
type MTBDDData v e = (IntMap (Node v e Index), Set e)

data MTBDD v e where
    MTBDD :: (Ord v, Ord e)
          => !Index         -- ^ Root node's index,
          -> MTBDDData v e  -- ^ MTBDD data.
          -> MTBDD v e

deriving instance (Eq e) => Eq (MTBDD v e)
deriving instance (Ord e) => Ord (MTBDD v e)

instance (Show v, Show e) => Show (MTBDD v e) where
    show bdd@(MTBDD t (c, tgts)) =
        concat [ "MTBDD {"
               , "core = "
               , show c
               , ", top = "
               , show t
               , ", tgts = "
               , show tgts
               , "}"
               , "\n"
               , toDot bdd
               ]

instance (NFData e) => NFData (MTBDD v e) where
    rnf (MTBDD t (c, v)) = rnf c `seq` rnf v `seq` rnf t

values :: MTBDD v e -> Set e
values (MTBDD _ (_, v)) = v

-- Construct the set of values in the BDD, along with their paths (a list of
-- var/direction pairs)
getPaths :: (Ord v, Ord e) => MTBDD v e -> Set ([(v, Bool)], e)
getPaths (MTBDD t (idmap, _)) = go t
  where
    go index = case idmap IM.! index of
                (Leaf set) -> S.singleton ([], set)
                (Branch vid l r) ->
                    let recAddCur b = S.map (first ((vid, b) :)) . go
                    in recAddCur False l `S.union` recAddCur True r

toDot :: (Show v, Ord v, Show e) => MTBDD v e -> String
toDot (MTBDD _ (idmap, _)) =
    unlines [ "digraph G {"
            , "compound=true"
            , leavesSubGraph
            , "node[shape=oval];"
            , unlinesNoTrailingNewline branchNodes
            , unlinesNoTrailingNewline . map showEdge $ branchEdges
            , "}"
            ]
  where
    unlinesNoTrailingNewline = intercalate "\n"

    (leaves, branchNodes, branchEdges) =
        processNodesAndBranchesPartitionEdges . IM.toList $ idmap

    processNodesAndBranchesPartitionEdges = foldr folder ([], [], [])
      where
        -- Generate the DOT nodes for leaves/branches and postpone the edges
        -- till later, so that we have already generated the required src/tgts.
        folder (nid, node) (ls, bs, es) = case node of
            Branch var lID rID ->
                let bStr = concat [ show nid
                                  , "[label=\""
                                  , show nid
                                  , " ~ "
                                  , show var
                                  , "\"];"
                                  ]
                in (ls, bStr : bs, (nid, lID, rID) : es)
            Leaf set ->
                ((show nid ++ "[label=\"" ++ show set ++ "\"];") : ls, bs, es)

    leavesSubGraph = unlinesNoTrailingNewline ["subgraph leaves {"
                                              , "rank=same;"
                                              , "node[shape=rectangle];"
                                              , unlinesNoTrailingNewline leaves
                                              , "}"
                                              ]

    showEdge (from, l, r) =
        unlinesNoTrailingNewline [ show from ++ "->" ++ show l ++ "[label=0];"
                                 , show from ++ "->" ++ show r ++ "[label=1];"
                                 ]

vars :: MTBDD v e -> Set v
vars (MTBDD _ (idmap, _)) = foldMap varsIn idmap
  where
    varsIn (Leaf _) = S.empty
    varsIn (Branch v _ _) = S.singleton v

-- Change variables in a MTBDD. The @f@ used must be monotone and injective, to
-- preserve invariants.
unsafeRevar :: (Ord v2) => (v1 -> v2) -> MTBDD v1 e -> MTBDD v2 e
unsafeRevar f = runEval . unsafeRevarM (return . f)

-- Change variables in a MTBDD. The @f@ used must be monotone and injective, to
-- preserve invariants.
unsafeRevarM :: (Monad m, Ord v2) => (v1 -> m v2) -> MTBDD v1 e
             -> m (MTBDD v2 e)
unsafeRevarM f (MTBDD t (c, vals)) = do
    c' <- mapM revarNode c
    return $ MTBDD t (c', vals)
  where
    revarNode (Leaf x) = return $ Leaf x
    revarNode (Branch v l r) = do
        v' <- f v
        return $ Branch v' l r

-- Rename the values in the MTBDD. The function must be injective, else it
-- might collapse distinct Leafs into one.
unsafeRename :: (e -> e) -> MTBDD v e -> MTBDD v e
unsafeRename f (MTBDD t (c, vals)) = MTBDD t (c', S.map f vals)
  where
    rename (Leaf e) = Leaf $ f e
    rename x = x

    c' = IM.map rename c

size :: MTBDD v e -> Int
size (MTBDD _ (c, _)) = IM.size c

emptyBDDData :: MTBDDData v e
emptyBDDData = (IM.empty, S.empty)

-- Access unfolds a single indirection of a branch, inlining the corresponding
-- left and right children.
access :: MTBDD v e -> Node v e (MTBDD v e)
access (MTBDD t dat@(c, _)) = case IM.lookup t c of
    Nothing -> error $ "MTBDD.Core.access of " ++ show t
    Just n -> case n of
        (Leaf x) -> Leaf x
        Branch v l r -> Branch v (MTBDD l dat) (MTBDD r dat)

data BuildState v e = BuildState
                        !(Map (Node v e Index) Index) -- ^ Inverse map
                        !Index                        -- ^ Next id
                    deriving ( Eq, Ord )

emptyState :: BuildState v e
emptyState = BuildState M.empty 0

type MTBDDCreateState v e = (BuildState v e, MTBDDData v e)
type BDDMakeT v e = StateT (MTBDDCreateState v e)

make :: (Monad m, Ord e, Ord v) => BDDMakeT v e m Index -> m (MTBDD v e)
make action = do
    (i, (_, dataBDD)) <- runStateT action (emptyState, emptyBDDData)
    i `seq` return $ MTBDD i dataBDD

-- register == Mk
-- Register checks that a particular node is known already (returning the
-- existing node's id if it is) and otherwise inserts it into the appropriate
-- maps and build caches.
register :: (Monad m, Ord v, Ord e) => Node v e Index -> BDDMakeT v e m Index
register n@(Leaf set) = do
    (BuildState inv i, (c, v)) <- get
    case n `M.lookup` inv of
        Just existing -> return existing
        Nothing -> do
            put ( BuildState (M.insert n i inv) (succ i)
                , (IM.insert i n c, S.insert set v)
                )
            return i
register n@(Branch _ l r)
    | l == r = return l -- Ensures we build reduced BDDs.
    | otherwise = do
        (BuildState inv i, (c, vs)) <- get
        case n `M.lookup` inv of
            Just existing -> return existing
            Nothing -> do
                put ( BuildState (M.insert n i inv) (succ i)
                    , (IM.insert i n c, vs)
                    )
                return i

-- Ensures binary/unary operations are only applied once per (pair of) index.
type OpCache v = IntIntMap v
type CachedT v = StateT (OpCache v)

withCache :: (Monad m) => CachedT v m v -> m v
withCache s = evalStateT s IIM.empty

cached :: (Monad m) => (Index, Index) -> CachedT v m v -> CachedT v m v
cached indices action = do
    c <- get
    case IIM.lookup indices c of
        Just i -> return i
        Nothing -> do
            i <- action
            modify $ IIM.insert indices i
            return i
