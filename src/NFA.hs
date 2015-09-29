{-# LANGUAGE TupleSections, GADTs, ScopedTypeVariables #-}
module NFA where

import Control.Applicative ( liftA2, (<$>) )
import Control.Arrow ( (***), (&&&), first )
import Control.DeepSeq ( NFData(..) )
import Control.Monad ( liftM )
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.State.Strict ( runState, gets, modify, get
                                        , evalState )
import Control.Monad.Trans.Writer ( runWriter, tell )
import qualified Data.Foldable as DF ( foldMap, foldrM, foldr1 )
import Data.Functor.Identity ( runIdentity )
import qualified Data.HashSet as HS
import qualified Data.IntSet as IS
import qualified Data.IntMap as IM
import Data.Maybe ( fromMaybe )
import Data.Monoid ( Any(..) )
import qualified Data.Set as S ( toList, insert, union, map, filter, (\\)
                               , singleton, null , deleteFindMin, notMember
                               , partition, member , foldr', foldr, empty
                               , fromList, size, findMin, toAscList, isSubsetOf
                               , findMax )
import Data.Set ( Set )
import qualified Data.Traversable as DT ( mapM )
import Data.List ( genericTake, intercalate, partition, sort )
import qualified Data.Map.Strict as M ( empty, toList, union, singleton, (!)
                                      , map, insertWith, foldrWithKey, insert
                                      , mapKeys, mapWithKey, toAscList
                                      , toDescList, delete, fromList
                                      , size, elems, lookup, notMember
                                      , deleteFindMin, null, fromAscList
                                      , mapAccumWithKey )
import Data.Map.Strict ( Map )

import qualified MTBDD ( (**), or, instantiateAllFalse, getPaths, unsafeRevar
                       , unary, values, unitWithVars, unaryM, constant, binary
                       , (||), (&&), unsafeRename )
import MTBDD.Internals
import MTBDD.Operation ( onBranchChildren, onNodes )

import Prelude hiding ( unlines )
import LTS ( LTS(..), statesLTS, LTSTransitionsBDD, TransitionBDD
           , addTransition )
import MapSetUtils ( setContainingEmptySet, crossSet, catSetMaybes, allSet
                   , numberSet, anySet, bigUnion, allMap, joinSet )
import Marking ( Marking, TokenStatus(..), WildCardMarking
               , wildCardMatchesMarking, setAtIndices, eqAtIndices )
import Nets ( NetWithBoundaries(..), NetTransition(..), unionNetTransition
            , inContention, selfConflicting )
import Util ( unlines, (.:) )

type SetFun a = a -> Bool

-- | An 'NFA' consists of an underlying LTS, and a (characteristic function
-- representation of) set of initial, and final states. The labels of the LTS
-- require an Ord instance, so we carry the constraint, to save annotations of
-- most type signatures involving BDDs.
data NFA s l where
    NFA :: (Ord s, Ord l) => LTS s l -> SetFun s -> SetFun s -> NFA s l

instance (Show s, Show l) => Show (NFA s l) where
    show nfa@(NFA lts isInit isFinal) =
        let states = statesLTS lts
        in concat [ "NFA ("
                  , show lts
                  , " ("
                  , show $ S.filter isInit states
                  , ") ("
                  , show $ S.filter isFinal states
                  , "))\n"
                  , nfa2Dot nfa
                  ]

instance (Eq s, Eq l) => Eq (NFA s l) where
    (NFA llts lisInit lisFinal) == (NFA rlts risInit risFinal) =
        llts == rlts && let states = statesLTS llts
                            go = (`S.filter` states)
                        in go lisInit == go risInit &&
                           go lisFinal == go risFinal

instance (NFData s) => NFData (NFA s l) where
    rnf (NFA lts isInit isFinal) = isInit `seq` isFinal `seq` rnf lts

-- | 'BoundarySide' is used to signify Which "side" of a NFAWithBoundaries we
-- are considering.
data BoundarySide = L
                  | R
                  deriving (Ord, Eq, Show)

-- | A 'BoundaryPos' is a position on a side of a 'NFAWithBoundaries'. E.g. the
-- topmost left boundary "port" would be represented as (0, L).
newtype BoundaryPos = BoundaryPos { unBoundaryPos :: (Int, BoundarySide) }
                    deriving (Eq)

-- This orders all left boundaries before right boundaries, numerically.
instance Ord BoundaryPos where
    (BoundaryPos (i, s)) <= (BoundaryPos (j, t)) = (s, i) <= (t, j)

instance Show BoundaryPos where
    show (BoundaryPos tuple) = show tuple

toBoundaryPos :: BoundarySide -> Int -> BoundaryPos
toBoundaryPos side = BoundaryPos . (, side)

-- | A 'NFAWithBoundaries' is a NFA over Boundary positions (i.e. the paths of
-- the MTBDD depend on whether a particular boundary port is active for a given
-- transition of the NFA).
data NFAWithBoundaries s = NFAWithBoundaries (NFA s BoundaryPos) !Int !Int
                       deriving (Eq)

instance (Show s) => Show (NFAWithBoundaries s) where
    show nfawb@(NFAWithBoundaries nfa l r) = concat [ "NFAWithBoundaries "
                                                    , show nfa
                                                    , " "
                                                    , show (l, r)
                                                    , "\n"
                                                    , nfaWB2Dot nfawb
                                                    ]

instance (NFData s) => NFData (NFAWithBoundaries s) where
    rnf (NFAWithBoundaries nfa l r) = rnf l `seq` rnf r `seq` rnf nfa

-- Takes a function to show paths, and a function to convert a transition map
-- into a map from (tagged) sources to tagged targets with the set of paths,
-- and use these to output a dot-formatted digraph.
nfa2DotHelper :: (Show s, Ord l) => NFA s l -> (p -> String)
              -> (LTSTransitionsBDD s l -> Map s (Map s (Set p)))
              -> String
nfa2DotHelper (NFA lts@(LTS origTrans) isInit isFinal) showPath toTrans =
    unlines [ "digraph SomeName {"
            , "node [shape = point]; init"
            , unlines stateLines
            , unlines . map outputDotTransitions . M.toList $ trans
            , "}"
            ]
  where
    states = M.fromAscList . zipWith (curry isInitFinal) [0..] . S.toAscList $
        statesLTS lts
    isInitFinal (i, s) = (s, (i, isInit s, isFinal s))

    (stateLines, _) = M.mapAccumWithKey collectStateLines [] states

    collectStateLines acc k v = (outputDotState k v : acc, ())

    trans = toTrans origTrans

    outputDotState name (i, isInitState, isFinalState) =
        concat [ show (i :: Integer)
               , " [label=\""
               , show name
               , "\" shape="
               , if isFinalState then "doublecircle" else "circle"
               , "];"
               , if isInitState then " init ->" ++ show i ++ ";" else ""
               ]

    outputDotTransitions (src, targs) =
            unlines . map (outputTransition src) . M.toList $ targs
      where
        getID s = (\(i,_,_) -> i) (states M.! s)

        outputTransition s (t, lbls) =
            unwords [ show $ getID s
                    , "->"
                    , show $ getID t
                    , "[label=\"{" ++ labels ++ "}\"];"
                    ]
          where
            labels = intercalate ", " . map showPath $ S.toList lbls

-- N.B. this function cannot know how many variables there should be in total,
-- so the labels will only show the values that are given in the BDD, in the
-- order that they appear in the BDD, without saying anything about missing
-- variables!
nfa2Dot :: (Show s) => NFA s l -> String
nfa2Dot nfa@NFA{} = nfa2DotHelper nfa showPath toTrans
  where
    toTrans = M.map (M.map (S.map S.fromList)) . curryAndTwistBDD

    showPath :: Set (v, Bool) -> String
    showPath = map (\(_, b) -> if b then '1' else '0') . S.toAscList

showNFAWBPath :: Set (BoundaryPos, BoolOrWild) -> String
showNFAWBPath path =
    let (ls, rs) = S.partition ((== L) . snd . unBoundaryPos . fst) path
        showSide = map showPathElem . S.toAscList
    in showSide ls ++ "/" ++ showSide rs
  where
    showPathElem (_, WildCard) = '*'
    showPathElem (_, B b) = if b then '1' else '0'

nfaWB2Dot :: (Show s) => NFAWithBoundaries s -> String
nfaWB2Dot (NFAWithBoundaries nfa@NFA{} l r) =
    nfa2DotHelper nfa showNFAWBPath (expandTransitions l r)

-- TODO: reduce code duplication between this and the 2Dot function
nfaWB2NFAOutput :: NFAWithBoundaries Int -> String
nfaWB2NFAOutput
    (NFAWithBoundaries (NFA lts@(LTS origTrans) isInit isFinal) l r) =
        unlines [ outputNFAStates $ filter isInit states
                , unlines . map outputNFATransitions . M.toList $
                    trans
                , outputNFAStates $ filter isFinal states
                ]
  where
    states = S.toList $ statesLTS lts
    trans = expandTransitions l r origTrans

    outputNFAStates [] = ""
    outputNFAStates [s] = show s
    outputNFAStates ss = intercalate "," $ map show ss

    outputNFATransitions (src, targs) =
            unlines . map (outputTransition src) . M.toList $ targs
      where
        outputTransition s (t, lbls) =
            concat [ show s
                   , "--"
                   , labels
                   , "->"
                   , show t
                   ]
          where
            labels = intercalate "," . map showNFAWBPath $ S.toList lbls

data BoolOrWild = B Bool
                | WildCard
                deriving ( Eq, Ord )

-- |expandTransitions expands a transition map, such that all paths in the
-- transition map are complete --- they mention every variable (BDDs don't
-- necessarily mention every variable, if its value is unimportant).
expandTransitions :: (Ord s) => Int -> Int
                  -> LTSTransitionsBDD s BoundaryPos
                  -> Map s (Map s (Set (Set (BoundaryPos, BoolOrWild))))
expandTransitions l r =
    M.map (M.map (S.map doExpandPath)) . curryAndTwistBDD
  where
    (lPortIDs, rPortIDs) = (toBoundaryPortIDs *** toBoundaryPortIDs) (l, r)
    toBoundaryPortIDs n = genericTake n [0..]

    doExpandPath :: [(BoundaryPos, Bool)] -> Set (BoundaryPos, BoolOrWild)
    doExpandPath path =
        let (ls, rs) = partition ((== L) . snd . unBoundaryPos . fst) path
            lExpanded = expandPath L lPortIDs ls
            rExpanded = expandPath R rPortIDs rs
        -- Sort the list to interleave it w.r.t. BoundaryPos ordering.
        in S.fromList . sort $ lExpanded ++ rExpanded

    -- expandPath takes a boundary side, a list of boundary ids, one per
    -- boundary port, and a list of explicitly given boundary values (a path),
    -- and generates an expanded list of boundary values that includes wild
    -- cards for any unspecified boundary port values.
    expandPath :: BoundarySide -> [Int] -> [(BoundaryPos, Bool)]
               -> [(BoundaryPos, BoolOrWild)]
    expandPath _ [] [] = []
    expandPath _ [] remaining@(_ : _) = error $
        "bad empty boundary list in expandPath: " ++ show remaining
    -- No more explicit variable values so the rest are wildcards.
    expandPath side iss@(_ : _) [] =
        zip (map (BoundaryPos . (, side)) iss) (repeat WildCard)
    -- Include a WildCard if the next boundary port is less than the next
    -- specified value's variable. If they are equal the particular boundary
    -- pos is specified in the path, so take the path's value.
    expandPath side (i : is) jss@((BoundaryPos (j, _), b) : js)
        | i < j = (BoundaryPos (i, side), WildCard) : expandPath side is jss
        | i == j = (BoundaryPos (i, side), B b) : expandPath side is js
        | otherwise = error "i index greater than j index in expandPath"

-- Turn a map of Int -> BDDs into a List of Int, Map Int (Set Path) pairs,
-- where the first Int is the source, the map key is the target and the set
-- is the set of paths between the source and target.
curryAndTwistBDD :: (Ord s, Ord l) => Map s (TransitionBDD s l)
                 -> Map s (Map s (Set [(l, Bool)]))
curryAndTwistBDD = M.map combiner
  where
    combiner bdd =
        let unionPath path tgt =
                M.insertWith S.union tgt (S.singleton path)
            unionPaths (path, tgts) pathMap =
                S.foldr (unionPath path) pathMap tgts
        in S.foldr unionPaths M.empty $ MTBDD.getPaths bdd

-- |negating an NFA simply makes all non-final states final.
negateNFA :: NFA s l -> NFA s l
negateNFA (NFA lts isInit isFinal) = NFA lts isInit (not . isFinal)

liftTransitions :: (Ord s, Ord l) => LTSTransitionsBDD s l -> Set s
                -> TransitionBDD s l
liftTransitions inputMap =
    MTBDD.or . map (`safeTransLookup` inputMap) . S.toList

-- Takes an NFA and renames the states starting from 0, in no particular order.
renumberNFA :: forall s l . (Ord l) => NFA s l -> NFA Int l
renumberNFA (NFA (LTS trans) isInit isFinal) =
    NFA (LTS trans') isInit' isFinal'
  where
    (trans', (_, initFinalMap)) = runState renamer (M.empty, M.empty)
    isInit' i = fst $ initFinalMap M.! i
    isFinal' i = snd $ initFinalMap M.! i

    renamer = mapKeysM numberState trans >>=
        DT.mapM (MTBDD.unaryM (mapSetM numberState))

    mapSetM :: (Monad m, Ord b) => (a -> m b) -> Set a -> m (Set b)
    mapSetM f = (S.fromList `liftM`) . mapM f . S.toList

    mapKeysM :: (Monad m, Ord j) => (k -> m j) -> Map k v -> m (Map j v)
    mapKeysM f = (M.fromList `liftM`) . mapM (firstM f) . M.toList

    firstM :: (Monad m) => (a -> m b) -> (a, c) -> m (b, c)
    firstM f (a, b) = (, b) `liftM` f a

    numberState s = do
        exists <- gets (M.lookup s . fst)
        case exists of
            Just r -> return r
            Nothing -> do
                next <- gets (fromIntegral . M.size . fst)
                let initFinal = (isInit s, isFinal s)
                modify (M.insert s next *** M.insert next initFinal)
                return next

-- Abstract over the particular cross product being performed (tensor or
-- sequential composition). In either case we want to calculate the
-- NFA-intersection, such that inits/finals of the crossed NFA are the pairs of
-- inits/finals.
crossNFA :: (TransitionBDD s l -> TransitionBDD t l -> TransitionBDD (s, t) l)
         -> NFA s l -> NFA t l -> NFA Int l
crossNFA crossTrans (NFA llts@(LTS ltrans) lisInit lisFinal)
                    (NFA rlts@(LTS rtrans) risInit risFinal)
     = renumberNFA $ NFA (LTS trans) isInit isFinal
  where
    isInit = uncurry (&&) . (lisInit *** risInit)
    isFinal = uncurry (&&) . (lisFinal *** risFinal)

    lStates = statesLTS llts
    rStates = statesLTS rlts

    -- This would be inefficient in general, since we might consider a large
    -- proportion of states to be initial. For our purposes, our NFAs generally
    -- have a single initial state, and so this shouldn't be a problem.
    linit = S.filter lisInit lStates
    rinit = S.filter risInit rStates
    inits = linit `crossSet` rinit

    trans = crossNFA' M.empty inits

    -- If both states have transitions, apply the crossTrans function,
    -- otherwise return Nothing.
    getTrans p q = liftA2 crossTrans (M.lookup p ltrans) (M.lookup q rtrans)

    crossNFA' transSoFar todo
        | S.null todo = transSoFar
        | otherwise =
            let (pq@(p, q), newTodo) = S.deleteFindMin todo
                (newTrans, todos) = case getTrans p q of
                    Nothing -> (M.empty, S.empty)
                    Just ts -> (M.singleton pq ts, bigUnion (MTBDD.values ts))
                transSoFar' = transSoFar `M.union` newTrans
                unseenTodos = S.filter (`M.notMember` transSoFar') todos
                todo' = newTodo `S.union` unseenTodos
            in crossNFA' transSoFar' todo'

-- Tensor of two nets places the nets on top of each other, without any
-- interaction. We implement tensor in terms of composition after tensoring
-- with identity nets:
--
-- A * B = (A * id) ; (id * B) which follows from bifunctoriality of tensor.
--
-- since we can only easily tensor (on the right) with nets that have an equal
-- number of boundaries on both sides.
tensor :: (Ord s, Ord t) => NFAWithBoundaries s -> NFAWithBoundaries t
       -> NFAWithBoundaries Int
tensor tnfawb@(NFAWithBoundaries _ _ tright)
       bnfawb@(NFAWithBoundaries _ bleft _) =
          fromMaybe (error "urk, internal error") $
              compose (withID True bleft tnfawb) (withID False tright bnfawb)
  where
    -- We need to account for the case where we'd be composed with a zero
    -- boundary, by not tensoring with any extra ID wires.
    withID _ 0 nfawb = modifyNFAWB renumberNFA nfawb
    withID isTop n nfawb =
        if isTop
            then tensor' False nfawb $ nIDNFA n (sizes nfawb)
            else tensor' True (nIDNFA n (0, 0)) nfawb

    sizes (NFAWithBoundaries _ l r) = (l, r)

    -- Make an n-identy wire NFAWB starting from boundaries @l@ and @r@. We
    -- can't just start at (0,0) and offset in the case where the identity wire
    -- is on the bottom, since if the top component has different sized
    -- boundaries we would reorder the variables in the identity component,
    -- breaking the MTBDD ordering invariant and causing obscure bugs.
    nIDNFA :: Int -> (Int, Int) -> NFAWithBoundaries Int
    nIDNFA n (l, r) = NFAWithBoundaries (NFA (LTS trans) (== 0) (== 0)) n n
      where
        trans = M.singleton 0 t0
        t0 = foldr1 (MTBDD.&&) $ zipWith ithID ls rs

        ls = [l..l+n-1]
        rs = [r..r+n-1]

    -- A path with value @b@ on the @i@-th left and @j@-th right boundary ports
    -- We sort the resulting list, to ensure we respect the order of the
    -- variables in the case where i > j, to avoid constructing an invalid path
    eqPath i j b = sort [(BoundaryPos (i, L), b), (BoundaryPos (j, R), b)]

    -- A BDD representing an identity wire at variable @i@ on the left and @j@
    -- on the right.
    ithID i j = MTBDD.unitWithVars S.empty (eqPath i j False) (S.singleton 0)
                MTBDD.||
                MTBDD.unitWithVars S.empty (eqPath i j True) (S.singleton 0)

    -- Offset the variables (i.e. boundaries) of the bottom component before
    -- crossing with the top component, we only need to do this when we don't
    -- know what the bottom component is. If we've constructed our special "id"
    -- component then we've already taken the top component's size into account
    tensor' shouldOffset
        (NFAWithBoundaries lnfa lleft lright)
        (NFAWithBoundaries rnfa@(NFA (LTS rtrans) rinit rfinals) rleft rright)
        = NFAWithBoundaries newNFA (lleft + rleft) (lright + rright)
      where
        newNFA = crossNFA (MTBDD.binary crossSet) lnfa rnfa'

        rnfa' = if shouldOffset then rnfaWithOffset else rnfa

        rnfaWithOffset = NFA (LTS rtrans') rinit rfinals

        -- N.B. Very Important! This is only safe when doOffset is monotone,
        -- i.e. when the left and right boundaries of the top component are the
        -- same size. Otherwise it can easily invalidate the ordering of the
        -- bottom component: e.g.
        --
        -- top component with one state 0 and single transition: 0--1/->0
        -- bottom component with one state 0 and two transitions: 0--0/0,1/1->0
        --
        -- the bottom component is then:
        --          0L
        --         /  \
        --        OR  OR
        --       /  \/  \
        --      /  null  \
        --      \        /
        --       \      /
        --        \    /
        --          {0}
        --
        -- clearly, offsetting 0L by one (to avoid the single left boundary of
        -- the top component) would make 1L, which should not appear above 0R
        -- since 1L > 0R!
        rtrans' = M.map (MTBDD.unsafeRevar doOffset) rtrans

        -- Offset the bottom transition variables
        doOffset (BoundaryPos (vid, side)) =
            let offset = case side of
                             L -> lleft
                             R -> lright
            in BoundaryPos (offset + vid, side)

-- each other in the MTBDD.
data CompVar = LVar Int
             | CommonVar (Int, BoundarySide)
             | RVar Int
             deriving (Eq, Ord, Show)

toCompVar :: Bool -> BoundaryPos -> CompVar
toCompVar isLeft (BoundaryPos (i, side)) = case side of
    L -> if isLeft then LVar i else CommonVar (i, side)
    R -> if isLeft then CommonVar (i, side) else RVar i

compose :: (Ord s) => NFAWithBoundaries s -> NFAWithBoundaries s
        -> Maybe (NFAWithBoundaries Int)
compose (NFAWithBoundaries lnfa lleft lright)
        (NFAWithBoundaries rnfa rleft rright)
    | lright /= rleft = Nothing
    | otherwise = Just $ NFAWithBoundaries newNFA lleft rright
  where
    newNFA = crossNFA commonSharedBDD lnfa rnfa

commonSharedBDD :: (Ord a, Ord b) => MTBDD BoundaryPos (Set a)
                -> MTBDD BoundaryPos (Set b)
                -> MTBDD BoundaryPos (Set (a, b))
commonSharedBDD bdd1 bdd2 =
        let bdd1' = unsafeRevar (toCompVar True) bdd1
            bdd2' = unsafeRevar (toCompVar False) bdd2
            crossed = MTBDD.binary crossSet bdd1' bdd2'
        in unsafeRevar fromCompVar .  purgeUnreachable .  removeSyncs $ crossed
  where

    fromCompVar (LVar i) = BoundaryPos (i, L)
    fromCompVar (RVar i) = BoundaryPos (i, R)
    fromCompVar cv = error $ "Unexpected compvar: " ++ show cv


    -- removeSyncs registers unused leaves, in any branches that are later
    -- unioned. This function simply restricts the MTBDD to Leaves/Branches
    -- that are reachable from the root.
    purgeUnreachable :: MTBDD v e -> MTBDD v e
    purgeUnreachable (MTBDD t (idmap, _)) = MTBDD t purgedData
      where
        purgedData = evalState (helper (getter t) t) S.empty
        getter i = idmap IM.! i

        helper l@(Leaf set) thisId =
            return (IM.singleton thisId l, S.singleton set)
        helper b@(Branch _ l r) thisId = do
            beenHere <- gets (thisId `S.member`)
            if beenHere
                then return (IM.empty, S.empty)
                else do
                    (lreach, lleaves) <- helper (getter l) l
                    (rreach, rleaves) <- helper (getter r) r
                    modify (thisId `S.insert`)
                    let reach = IM.insert thisId b $ lreach `IM.union` rreach
                    return (reach, lleaves `S.union` rleaves)

    removeSyncs :: (Ord e) => MTBDD CompVar (Set e) -> MTBDD CompVar (Set e)
    removeSyncs = runIdentity . make . withCache . go
      where
        makeFromState i = MTBDD i . snd <$> lift get

        go x@(MTBDD t _) = cached (t, t) $
            case access x of
                Leaf p -> registerInCache $ Leaf p
                b@(Branch v l r) ->
                    if shouldStop v
                        then reregister b
                        else do
                            (wasSync, l', r') <- processChildren v l r
                            if wasSync || shouldElim v
                                then do
                                    lBDD <- makeFromState l'
                                    rBDD <- makeFromState r'
                                    doUnion lBDD rBDD
                                else registerInCache $ Branch v l' r'

        -- TODO: This is horrible, can we improve our node map such that we can
        -- somehow simply union in the subtree rather than re-registering it?
        reregister (Leaf p) = registerInCache $ Leaf p
        reregister (Branch v l r) = do
            l' <- reregister $ access l
            r' <- reregister $ access r
            registerInCache $ Branch v l' r'

        registerInCache = lift . register

        processChildren v l r = case (access l, access r) of
            (Leaf x, Leaf y) -> do
                lRes <- registerInCache $ Leaf x
                rRes <- registerInCache $ Leaf y
                return (False, lRes, rRes)
            (Leaf x, Branch v2 _ r2) -> do
                let rSync = syncWith v v2
                lRes <- registerInCache $ Leaf x
                rRes <- go $ if rSync then r2 else r
                return (rSync, lRes, rRes)
            (Branch v1 l1 _, Leaf y) -> do
                let lSync = syncWith v v1
                lRes <- go $ if lSync then l1 else l
                rRes <- registerInCache $ Leaf y
                return (lSync, lRes, rRes)
            (Branch v1 l1 _, Branch v2 _ r2) -> do
                let lSync = syncWith v v1
                    rSync = syncWith v v2
                lRes <- go $ if lSync then l1 else l
                rRes <- go $ if rSync then r2 else r
                return (lSync || rSync, lRes, rRes)

        shouldStop (RVar _) = True
        shouldStop _ = False

        syncWith (CommonVar (i, L)) (CommonVar (j, R)) = i == j
        syncWith _ _ = False

        shouldElim (CommonVar _) = True
        shouldElim _ = False

        doUnion l r = withCache $ unioner l r
          where
            -- Union two MTBDDs, but using a fresh cache each time, since we'll be
            -- traversing different nodes with (potentially) the same identities
            -- several times, and therefore can't use a cache.
            unioner :: (Ord e, Monad m, Ord v) => MTBDD v (Set e) -> MTBDD v (Set e)
                    -> CachedT Index (CachedT Index (BDDMakeT v (Set e) m)) Index
            unioner x@(MTBDD tx _) y@(MTBDD ty _) =
                let avoidCaches = lift . lift
                    -- Lift register through the caches
                    liftReg = avoidCaches . register
                    -- Apply the given operation and register the resulting Leaf
                    onLeaves l1 l2 = do
                        res <- avoidCaches $ return (l1 `S.union` l2)
                        liftReg . Leaf $ res
                    onBranch v = onBranchChildren unioner (liftReg .: Branch v)
                in cached (tx, ty) $ onNodes onLeaves onBranch x y

subsetConstruction :: (Ord l) => NFA s l -> NFA (Set s) l
subsetConstruction = subsetConstructionHelper id (const id)

epsilonSubsetConstruction :: NFA s l -> NFA (Set s) l
epsilonSubsetConstruction nfa@(NFA (LTS trans) _ _) =
    subsetConstructionHelper epsilonLookup MTBDD.unary nfa
  where
    epsilonLookup tgts = tgts `S.union` joinSet lookupOrEmpty tgts

    -- A particular state may not have any transitions (and therefore no eps
    -- transitions) so return the emptyset if it doesn't appear in the map.
    lookupOrEmpty i = fromMaybe S.empty $ M.lookup i epsilonMap

    epsilonMap = transitivelyCloseMap $ M.map instantiateAllToFalse trans

-- Make an epsilon-move (i.e. all variables are 0)
instantiateAllToFalse :: (Ord s, Ord v) => TransitionBDD s v -> Set s
instantiateAllToFalse = MTBDD.instantiateAllFalse

-- |This helper takes two functions, one to modify states, and one to lift that
-- function to a modification function on transitions. This is used to share
-- implementation between the epsilonSubsetConstruction, which expands all
-- states into the epsilon closure of those states.
-- Even though we return a NFA, each transition will map into a singleton set,
-- rather than a set of states, so it is infact a DFA, as expected.
subsetConstructionHelper :: (Ord l) => (Set s -> Set s)
                         -> ((Set s -> Set s)
                                -> TransitionBDD s l
                                -> TransitionBDD s l)
                         -> NFA s l -> NFA (Set s) l
subsetConstructionHelper transformStates liftToTrans
    (NFA lts@(LTS origtrans) isInit isFinal) =
    NFA (LTS trans') isInit' isFinal'
  where
    modifiedInits = transformStates . S.filter isInit $ statesLTS lts

    isInit' i = i == modifiedInits

    singleInits = S.singleton modifiedInits
    (states', trans') = helper M.empty singleInits singleInits

    -- The new finals are any state set that contains an original final state
    isFinal' i = i `S.member` finals

    finals = S.filter (anySet isFinal) states'

    helper transSoFar done todo
        | S.null todo = (done, transSoFar)
        | otherwise =
            let (p, newTodo) = S.deleteFindMin todo
                lifted = liftTransitions origtrans p
                transFromP = liftToTrans transformStates lifted
                -- Which new states haven't we seen before?
                todoStates =
                    S.filter (`S.notMember` done) . MTBDD.values $ transFromP
                transSoFar' = M.insert p (MTBDD.unary S.singleton transFromP) transSoFar
                done' = done `S.union` todoStates
                todo' = newTodo `S.union` todoStates
            in helper transSoFar' done' todo'

data BoundarySignal = Signal
                    | NoSignal
                    deriving (Eq, Ord, Show)

type BoundarySignals = Map Int BoundarySignal

signalsMapToBDD :: (Ord s) => Map (BoundarySignals, BoundarySignals) (Set s)
                -> TransitionBDD s BoundaryPos
signalsMapToBDD =
    let to :: BoundarySide -> BoundarySignals -> [(BoundaryPos, Bool)]
        to side = M.elems .
            M.mapWithKey (curry $ toBoundaryPos side *** (== Signal))
        -- The definition of Ord for Pairs and BoundarySide ensures
        -- that we get: [(0,L),(0,R),(1,L),(1,R),(2,L)]
        interleave = sort . uncurry (++) . (to L *** to R)
        doUnit = uncurry (MTBDD.unitWithVars S.empty) . first interleave
    in MTBDD.or . map doUnit . M.toList

-- TODO: check that ports are not outside the range of the NetWithBoundaries
--       both boundaries and places...
toNFA :: NetWithBoundaries -> NFAWithBoundaries Int
toNFA = toNFAWithFinals False Nothing

toNFAWithMarking :: Bool -> WildCardMarking -> NetWithBoundaries
                 -> NFAWithBoundaries Int
toNFAWithMarking i wc = toNFAWithFinals i $ Just (wildCardMatchesMarking wc)

toNFAWithFinals :: Bool -> Maybe (SetFun Marking) -> NetWithBoundaries
                -> NFAWithBoundaries Int
toNFAWithFinals useInterleaving mbFinals
    (NetWithBoundaries l r _ mark iTrans eTrans) =
        NFAWithBoundaries (NFA lts isInit isFinal) l r
  where
    nTrans = iTrans `HS.union` eTrans
    lts = LTS $ M.map signalsMapToBDD ltsTrans

    isInit = (== initID)

    -- The ID of the initial state
    initID = stateToID M.! mark

    -- Lookup the given ID in the map, unless we have no Finals function, in
    -- which case, everything is final
    isFinal i = maybe True (const (idToIsFinal M.! i)) mbFinals

    ltsTrans = renumberTrans trans'
    renumberTrans = M.mapKeys getStateID . M.map (M.map (S.map getStateID))
    getStateID = (stateToID M.!)

    (stateToID, idToState) = numberSet states'
    idToIsFinal = M.map lookupFinal idToState
    lookupFinal s = maybe True ($ s) mbFinals

    singleMark = S.singleton mark
    (states', trans') = toNFA' M.empty singleMark singleMark

    nNoSignals n = M.fromList $ map (, NoSignal) [0..n-1]
    lEmptyMarking = nNoSignals l
    rEmptyMarking = nNoSignals r

    markingSignalsAt is = M.fromAscList $ zip (IS.toAscList is) (repeat Signal)

    fire :: Marking -> Set NetTransition
         -> ((BoundarySignals, BoundarySignals), Marking)
    fire m ts
        | S.null ts = ((lEmptyMarking, rEmptyMarking), m)
        | otherwise =
            let (NetTrans lefts consume produce _ rights _) =
                    DF.foldr1 unionNetTransition ts
                consumeNotProduce = consume IS.\\ produce
                m' = flip (setAtIndices Present) produce $
                        setAtIndices Absent m consumeNotProduce
                -- Mark the boundaries corresponding to the transitions being fired
                leftLabel = (`M.union` lEmptyMarking) . markingSignalsAt $ lefts
                rightLabel = (`M.union` rEmptyMarking) . markingSignalsAt $ rights
            in ((leftLabel, rightLabel), m')

    enabled ts m = HS.filter (isEnabled m) ts

    -- Remove any transitions that can never be fired due to self-conflict
    eligibleTrans = HS.filter (not . selfConflicting) nTrans

    -- Memoise here, prevent notInConflict calls on repeated arguments?
    -- Seems to be linear growth in memory consumption, do we need to force
    -- things? Check

    toNFA' :: Map Marking
                  (Map (BoundarySignals, BoundarySignals) (Set Marking))
           -> Set Marking
           -> Set Marking
           -> (Set Marking, Map Marking
                                (Map (BoundarySignals, BoundarySignals)
                                     (Set Marking)))
    toNFA' transSoFar done todo
        | S.null todo = (done, transSoFar)
        | otherwise =
            let (m, newTodo) = S.deleteFindMin todo
                -- Find all sets of transitions which don't conflict and that
                -- are enabled for the chosen marking
                enabledTrans = hashSetToSet $ enabled eligibleTrans m
                toFire = if useInterleaving
                    then S.insert S.empty $ S.map S.singleton enabledTrans
                    else notInConflict enabledTrans
                fired = S.map (fire m) toFire
                mPrimes = S.map snd fired
                -- Find all the states which we've not yet visited
                newStates = mPrimes S.\\ done
                todo' = newTodo `S.union` newStates
                -- Insert the union of each fired transition with the existing
                -- transition map
                combiner (lbl, tgt) =
                    M.insertWith S.union lbl (S.singleton tgt)
                transSoFar' =
                    M.insert m (S.foldr' combiner M.empty fired) transSoFar
                done' = done `S.union` newStates
            in toNFA' transSoFar' done' todo'

    hashSetToSet = S.fromList . HS.toList

-- A given NetTransition is enabled, if all its consume/query places are
-- marked, and none of its produce places are marked.
isEnabled :: Marking -> NetTransition -> Bool
isEnabled m (NetTrans _ consume produce query _ _) =
    let -- Are all query ports marked?
        queryMarked = eqAtIndices Present m query
        -- Are all the consume ports marked?
        consumedMarked = eqAtIndices Present m consume
        -- Those ports that are produce ports, but not also consume
        -- ports. This lets tokens "pass through" a node in one step. The
        -- particular definition of conflicting transitions will influence
        -- whether this "pass through" is ever needed.
        producedNotConsumed = (produce IS.\\ consume)
        -- Are all produce (but not consume) ports unmarked?
        producedNotConsumedUnMarked = eqAtIndices Absent m producedNotConsumed
    in consumedMarked && queryMarked && producedNotConsumedUnMarked

-- Construct the set of sets of transitions that are not conflicting.
-- Conflicting transitions share ports, or have a query and non query of the
-- same place.
notInConflict :: Set NetTransition -> Set (Set NetTransition)
notInConflict = S.foldr' combine setContainingEmptySet
  where
    combine t ps = ps `S.union` catSetMaybes (S.map (addIfNonConflicting t) ps)

    addIfNonConflicting t s =
        if doesntConflictWith t s then Just $ t `S.insert` s else Nothing

    doesntConflictWith t = allSet (not . inContention t)


reverseNFA :: NFA s l -> NFA s l
reverseNFA (NFA (LTS trans) inits finals) = NFA (LTS ltsTrans) finals inits
  where
    ltsTrans = M.map (MTBDD.or . map toOBDD) tgtPathMap

    -- Construct a map from target -> [(path, orig source)]
    tgtPathMap = M.foldrWithKey srcPathFolder M.empty $
        -- A set of paths, for each source state
        M.map MTBDD.getPaths trans

    -- Fold over each (src, set of paths) pair, making each original source a
    -- singleton "target".
    srcPathFolder origSrc paths newTrans =
        S.foldr (pathFolder (S.singleton origSrc)) newTrans paths

    -- Fold over the set of paths for a given src
    pathFolder origSrc (path, origTgts) transMap =
        S.foldr (targetFolder origSrc path) transMap origTgts

    -- Fold over each target for a given (src, path) pair
    targetFolder origSrc path origTgt =
        M.insertWith (++) origTgt [(path, origSrc)]

    -- Construct the MTBDD.
    toOBDD = uncurry (MTBDD.unitWithVars S.empty)

reflexivelyCloseMap :: (Eq k, Ord k) => Map k (Set k) -> Map k (Set k)
reflexivelyCloseMap = M.mapWithKey S.insert

transitivelyCloseMap :: (Eq k, Ord k) => Map k (Set k) -> Map k (Set k)
transitivelyCloseMap = folder . forwards . folder . backwards
  where
    folder = uncurry (foldr listFolder)

    forwards = id &&& M.toAscList
    backwards = id &&& M.toDescList

    -- For each target set, expand the targets into their epsilon closure.
    listFolder (k, eps) = M.map (unioner k eps)

    unioner k eps s = if k `S.member` s then eps `S.union` s else s


-- Brzozowski's algorithm for DFA minimisation
epsMinimiseNFA :: (Ord l) => NFA s l -> NFA Int l
epsMinimiseNFA = renumberNFA .
    subsetConstruction . reverseNFA . epsilonSubsetConstruction . reverseNFA

epsMinimise :: NFAWithBoundaries s -> NFAWithBoundaries Int
epsMinimise = modifyNFAWB epsMinimiseNFA

-- An epsilon map records the set of states that are reachable by (>=1)
-- epsilon transitions.
type EpsilonMap s = Map s (Set s)

epsilonCloseNFA :: forall s l . NFA s l -> NFA s l
epsilonCloseNFA (NFA (LTS trans) isInit isFinal) =
    NFA (LTS trans') isInit isFinal'
  where
    isFinal' x = isFinal x || anySet isFinal (safeEpsLookup x)

    -- If all states can only map to themselves on epsilon, nothing needs
    -- to be done, so fail fast.
    trans' = if allMap ((== 1) . S.size) epsilonMap
                 then trans
                 else M.mapWithKey preComposeWithEps trans

    preComposeWithEps state obdd = MTBDD.or $
        -- The original bdd, and all bdds reachable from epsilon.
        (obdd :) . map (`safeTransLookup` trans) . S.toList $
            epsilonMap M.! state

    epsilonMap = transitivelyCloseMap $ M.map instantiateAllToFalse trans

    -- A given state may not have any transitions, so wouldn't be in emap
    safeEpsLookup = fromMaybe S.empty . (`M.lookup` epsilonMap)

-- A given state may have no transitions (and so not appear in trans),
-- so return the null bdd in this case. For example, this can occurr
-- when reversing a nfa: 0 -a-> 1, state 0 will appear in the target of
-- 1, but has no transitions since nothing maps into it.
safeTransLookup :: (Ord s, Ord l) => s -> Map s (TransitionBDD s l)
                -> TransitionBDD s l
safeTransLookup = fromMaybe (MTBDD.constant S.empty) .: M.lookup

-- A Block is just a subset of the places of a NFA.
type Block s = Set s

-- A Partition is a Set of (non-empty) Blocks that covers the places of an NFA
-- (with no overlap). N.B. the types don't enforce these properties.
type Partition s = Set (Block s)

-- A split will either partition a block, or leave it as is
data SplitRes s = NoSplit (Block s)
                | Split (Block s) (Block s)
                deriving (Eq, Ord)

-- | Turn a SplitRes into a Set of blocks and a Bool indicating if the original
-- SplitRes was a Split or not.
splitResToBlocks :: (Ord s) => SplitRes s -> (Any, Set (Block s))
splitResToBlocks (NoSplit b) = (Any False, S.singleton b)
splitResToBlocks (Split b1 b2) = (Any True, S.fromList [b1, b2])

quotientByPartition :: Partition s -> NFA s l -> (NFA s l, Any)
quotientByPartition p nfa@(NFA (LTS trans) isInit isFinal)
    | allSet ((== 1) . S.size) p = (nfa, Any False)
    | otherwise = runWriter $ do
        -- Remove any redundent keys.
        trans' <- DF.foldrM deleteEquivSources trans splitP
        -- Remove any equivalent targets.
        trans'' <- DT.mapM (MTBDD.unaryM quotientSet) trans'
        return $ NFA (LTS trans'') isInit' isFinal'
  where
    -- Remove the element that we can think of the remaining elements in the
    -- equivalence class as reducing to.
    splitP = S.foldr inserter S.empty p

    inserter s sofar =
        let split@(_, rest) = S.deleteFindMin s
            adder = if S.null rest then id else (split `S.insert`)
        in adder sofar

    -- Partitions should respect final states, but not necessarily initial
    -- states. That is, we might collapse a initial state into a non-initial
    -- state, so must check through the partitions to check for initiality.
    isFinal' = isFinal
    isInit' x =
        -- Find the partitions that the element is in, this will be a singleton
        -- set, unless we don't have a real partition. An elem is initial if
        -- any of its equivalence class is.
        let memberOf = S.filter (x `S.member`) p
        in case S.toList memberOf of
            [es] -> anySet isInit es
            _ -> error "Invalid partition in quotientByPartition."

    setModified = tell (Any True)

    quotientSet set = DF.foldrM quotientTargets set splitP
    quotientTargets (equivTo, equivRest) set
        | S.null equivRest = return set -- Singleton equivalence class
        | otherwise =
            -- If any of the equivalent states are in the target set, remove
            -- them, and insert the equivalent to state. Otherwise, do nothing.
            let set' = set S.\\ equivRest
            in if S.size set' /= S.size set -- Was anything removed?
                then do
                    setModified
                    return $ S.insert equivTo set'
                else return set

    deleteEquivSources (equivTo, equivRest) transMap
        | S.null equivRest = return transMap
        | otherwise =
            -- Get the BDDs of the sources we're merging
            let toDelete = catSetMaybes $ S.map (`M.lookup` transMap) equivRest
            -- If none of them were in the map, we're done
            in if S.null toDelete
                then return transMap
                else do
                    setModified
                    let remaining = equivTo `safeTransLookup` transMap
                        -- Ensure we don't lose any transitions from the
                        -- equivalence class, by unioning the transitions of
                        -- all the to-be-deleted sources.
                        unioned = S.foldr (MTBDD.||) remaining toDelete
                        trans' = S.foldr M.delete transMap equivRest
                    return $ M.insert equivTo unioned trans'

-- Algorithm of Kanellakis and Smolka. We iteratively refine a partition P of
-- the states of the NFA, starting with the coarsest partition: the singleton
-- set of all states. The refinement of a block in P, B, is performed by
-- finding a label on which elements of B transition to different subsets of P.
-- Given a partition, we can collapse elements of the partitions, giving an
-- equivalent NFA.
-- The seemingly unnecessary match brings the NFA's constraints into scope.
epsBisimEquiv :: forall l . NFA Int l -> NFA Int l
epsBisimEquiv inputNFA@(NFA{}) =
    if S.size states <= 1
        then inputNFA
        else let (accepts, rejects) = S.partition origIsFinal $ statesLTS lts
                 -- We might have no non-final states, so remove the empty
                 -- block. An invariant is that we should never construct
                 -- an empty block in a partition.
                 initPartition =
                    S.fromList [accepts, rejects] S.\\ S.singleton S.empty
                 finalPart = refinePartition initPartition
            in fst $ quotientByPartition finalPart epsClosedNFA
  where
    epsClosedNFA@(NFA lts@(LTS origTrans) _ origIsFinal) =
        epsilonCloseNFA inputNFA

    states = statesLTS lts

    refinePartition :: Partition Int -> Partition Int
    refinePartition p =
        let splitBlocks = S.map (split p) p
        -- Try splitting each block of the partion, combining the results.
        in case DF.foldMap splitResToBlocks splitBlocks of
            (Any False, _) -> p
            (Any True, splitres) -> refinePartition splitres

    -- Take a transformation function @tran@ and apply it to the two set
    -- partitions generated by the predicate @predicate@.
    partitionModify :: (Ord r) => (e -> r) -> (e -> Bool) -> Set e
                   -> (Set r, Set r)
    partitionModify tran predicate =
        let transform = S.map tran
        in (transform *** transform) . S.partition predicate

    -- Given the current partition @p@, and a block @block@ in @p@, partition
    -- the @block@ by equality on the set of blocks in @p@ reachable.
    split :: Partition Int -> Block Int -> SplitRes Int
    split p block
        | S.size block == 1 = NoSplit block
        | otherwise =
            -- Partition by equality on BDDs, first mapping the targets into
            -- their partitions. Places with equal BDDs are indistinguisable.
            let placeAndBlocks = S.map (id &&& lookupBlocks) block
                lookupBlocks = (`safeTransLookup` transBlocks p)
                el = snd $ S.findMin placeAndBlocks
                sameTrans = (== el) . snd
                (eqEl, neqEl) = partitionModify fst sameTrans placeAndBlocks
            in if S.null neqEl
                   then NoSplit block
                   else Split eqEl neqEl

    -- Convert a BDD mapping into sets of states into a BDD mapping into sets
    -- of block ids, given particular partition.
    transBlocks :: Partition Int -> Map Int (TransitionBDD Int l)
    transBlocks p = M.map (MTBDD.unary $ S.map lookupBlockID) origTrans
      where
        lookupBlockID = (blockIDs p M.!)

    -- Assign each block in a partition a unique natural, then return u Map
    -- from each NFA state to its block ID.
    blockIDs :: Partition Int -> Map Int Int
    blockIDs p =
        let flattenBlock (b, bId) = map (, bId) $ S.toList b
        in M.fromList . concatMap flattenBlock $ zip (S.toList p) [0..]

-- | 'modifyNFAWB' uses a passed function to modify the internals of an
-- NFAWithBoundaries, without modifying the boundaries.
modifyNFAWB :: (NFA s BoundaryPos -> NFA t BoundaryPos)
            -> NFAWithBoundaries s -> NFAWithBoundaries t
modifyNFAWB f (NFAWithBoundaries nfa l r) = NFAWithBoundaries (f nfa) l r

reflexivelyCloseNFA :: NFAWithBoundaries s -> NFAWithBoundaries s
reflexivelyCloseNFA (NFAWithBoundaries (NFA lts@(LTS trans) i f) l r) =
    NFAWithBoundaries (NFA lts' i f) l r
  where
    lts' = M.foldrWithKey addEpsLoop lts trans
    addEpsLoop src _ toLTS = addTransition toLTS src epsilon src

    -- Sort to obtain correct var order, and map each to false i.e. the label:
    -- 0^l / 0^r
    epsilon = map (, False) . sort $ toBPos L l ++ toBPos R r

    toBPos side count =
        map (BoundaryPos . (, side)) . genericTake count $ [0..]

-- HKC algorithm of Bonchi and Pous for checking NFA equivalence.
equivalenceHKC :: NFA Int l -> NFA Int l -> Bool
equivalenceHKC (NFA llts@(LTS lTrans) lIsInit lIsFinal)
               (NFA rlts@(LTS rTrans) rIsInit rIsFinal) =
    equivalenceHKC' lInits rInits (NFA (LTS trans) isInit isFinal)
  where
    lStates = statesLTS llts

    offset = if S.null lStates then 0 else 1 + S.findMax lStates

    doOffset = (+ offset)
    undoOffset = subtract offset

    lInits = S.filter lIsInit lStates
    rInits = S.map doOffset . S.filter rIsInit $ statesLTS rlts

    trans = lTrans `M.union` rTrans'

    changeMTBDD = MTBDD.unsafeRename (S.map doOffset)
    rTrans' = M.mapKeys doOffset . M.map changeMTBDD $ rTrans

    isInit x = if x `S.member` lStates
                  then lIsInit x
                  else rIsInit (undoOffset x)

    isFinal x = if x `S.member` lStates
                    then lIsFinal x
                    else rIsFinal (undoOffset x)

-- Checks for the equivalence of sets of states @sx@ and @sy@ in the given NFA.
equivalenceHKC' :: forall s l . Set s -> Set s -> NFA s l -> Bool
equivalenceHKC' ix iy (NFA (LTS trans) _ isFinal) =
    loop M.empty (S.singleton (ix, iy))
  where
    loop :: Map (Set s) (Set s) -> Set (Set s, Set s)
         -> Bool
    loop r todo
        | S.null todo = True
        | fx == fy = loop r todo'
        | otherwise = let r' = extendR r fx fy
                          todo'' = S.union (getCommonTargets x y) todo'
                      in setIsAccepting x == setIsAccepting y && loop r' todo''
      where
        ((x, y), todo') = S.deleteFindMin todo
        (fx, fy) = (followCtx r x, followCtx r y)

    -- Extend the relation by adding in the union of the expanded sets, saving
    -- space by not relating equal sets (when an expanded set equals the union
    -- of both union).
    extendR r fx fy
        | fx == fxy = M.insert fy fxy r
        | fy == fxy = M.insert fx fxy r
        | otherwise = M.insert fy fxy $ M.insert fx fxy r
      where
        fxy = fx `S.union` fy

    -- Rewrite a given set into its normal form w.r.t. the relation's
    -- congruence closure.
    followCtx r x = followCtx' [] False x r
    followCtx' skipped changed s r
        | M.null r =
            if changed
                -- If we changed something, we might be able to now use (some
                -- of) the skipped elements.
                then followCtx' [] False s (M.fromList skipped)
                else s
        | otherwise =
            let (xy@(x, y), r') = M.deleteFindMin r
            in if x `S.isSubsetOf` s
                   then let sy = S.union s y
                            -- If y is a subset of s then we haven't changed.
                            changed' = changed || s /= sy
                        in followCtx' skipped changed' sy r'
                   else followCtx' (xy : skipped) changed s r'

    setIsAccepting s = not (S.null s) && anySet isFinal s

    getCommonTargets x y =
        let xTargets = liftTransitions trans x
            yTargets = liftTransitions trans y
        in MTBDD.values $ xTargets MTBDD.** yTargets
