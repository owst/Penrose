{-# LANGUAGE TupleSections, ScopedTypeVariables, CPP #-}
module Minimisation where

import Control.Arrow ( (&&&) )

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative ( (<$>), Applicative )
#endif

import Control.Monad ( when )
-- Eval is a strict identity monad.
import Control.Parallel.Strategies ( runEval )
import Control.Monad.Trans.Writer ( WriterT, runWriterT, tell, writer, listen )
import qualified Data.Foldable as DF ( foldrM, any )
import Data.Maybe ( fromMaybe )
import Data.Map ( Map )
import qualified Data.Map.Strict as M ( traverseWithKey, insert, insertWith, map
                               , empty, keysSet, (!), unionWith, foldrWithKey
                               , delete, lookup, singleton, keys )
import Data.Monoid ( Any(..), All(..) )
import Data.Set (Set)
import qualified Data.Set as S ( empty, singleton, filter, fold, intersection
                               , (\\), size, union, map, null, foldr, partition
                               , delete, insert )
import qualified Data.Traversable as DT ( mapM )

import MapSetUtils
import NFA
import LTS ( LTS(..), LTSTransitionsBDD, TransitionBDD, statesLTS )
import Util ( (.:) )

import qualified MTBDD
import MTBDD.Internals

type Rel s = Map s (Set s)

-- invert a relation
invertRel :: (Ord s) => Rel s -> Rel s
invertRel = M.foldrWithKey folder M.empty
  where
    folder src tgts m =
        let srcSet = S.singleton src
        in S.foldr (\tgt -> M.insertWith S.union tgt srcSet) m tgts

-- Get the partition induced by a relation, which is assumed to be transitive.
toPart :: (Ord s) => Rel s -> Set (Set s)
toPart rel = intersected S.\\ S.singleton S.empty
  where
    -- a = b iff a <= b and b <= a, but only when <= is transitively closed.

    intersected = S.map intersectRel $ M.keysSet rel
    intersectRel s = S.intersection (rel M.! s) (inv M.! s)
    inv = invertRel rel

-- Asymmetric restriction of a relation, which is assumed to be transitive.
asymmetricRestriction :: (Ord s) => Rel s -> Rel s
asymmetricRestriction rel = M.unionWith (S.\\) rel $ invertRel rel

-- |@iterateWhile action input@ iterates @action@ on @input@ until it returns
-- False meaning that a fixed point has been reached.
iterateWhile :: (Monad m, Functor m) => (s -> WriterT Any m s) -> s -> m s
iterateWhile action = (fst <$>) . runWriterT . go
  where
    go input = do
        (output, Any didChange) <- listen $ action input
        if didChange
            then go output
            else return output

-- Minimisation function:
-- take an integer (lookahead), and an nfa, and minimise it
-- repeating the following operations, until a fixpoint is reached
--  1) remove dead states
--  2) prune transitions
--  3) quotient
minimise :: Int -> NFA s l -> NFA s l
minimise k = runEval . iterateWhile step
  where
    step nfa@NFA{} = do
        -- Remove any initially dead states of the NFA
        nfa' <- removeDead nfa
        let rel = generateSimRel nfa' k
        pruned <- modifyLTS (\l -> prune l (asymmetricRestriction rel)) nfa'
        -- Pruning may make states dead, so remove them
        noDeadInPruned <- removeDead pruned
        -- We may have removed states involved in rel, so regenerate it
        let rel' = generateSimRel noDeadInPruned k
        -- Quotient equivalent (w.r.t. lookahead simulation) states
        writer $ quotientByPartition (toPart rel') noDeadInPruned

-- Modify the LTS of an NFA using the supplied function
modifyLTS :: (Monad m) => (LTS s l -> m (LTS s l)) -> NFA s l -> m (NFA s l)
modifyLTS f (NFA l isI isF) = do
    l' <- f l
    return $ NFA l' isI isF

-- Remove dead states function, where a state is dead if it is unreachable from
-- an initial state.
-- take an nfa, a set of states and remove states from nfa
removeDead :: (Monad m) => NFA s l -> WriterT Any m (NFA s l)
removeDead nfa@(NFA (LTS m) isInit isFinal)
    | S.null dead = return nfa
    -- If we are going to kill all the states we should preserve a single
    -- (non-final) initial state. This is because some parts of the code assume
    -- non-empty NFAs. TODO: remove those parts and this hack. Don't set the
    -- flag, since we have nothing else to do, so we don't need to recurse any
    -- more.
    | allDead = return singletonNFA
    | otherwise = setFlag >> return (NFA (LTS m') isInit isFinal)
  where
    -- An NFA with a single initial state with a self-loop.
    singletonNFA =
        let sing = -- This assumes that the key map is non-empty, i.e. there
                   -- are some states in the NFA, and will fail if not.
                   -- Arbitrarily take the 0'th state as the singleton state.
                   head (M.keys m)
            singMap =  M.singleton sing (MTBDD.constant $ S.singleton sing)
        in NFA (LTS singMap) (== sing) (const False)

    -- First delete dead sources, then dead targets
    m' = M.map (removeStates dead) $ S.foldr M.delete m dead

    (allDead, dead) = deadStates nfa

    removeStates states bdd = MTBDD.binary (S.\\) bdd (MTBDD.constant states)

-- |'deadStates' takes an nfa and returns the set of dead states, i.e. those
-- that cannot be reached from an initial state, or those that do not ever
-- reach a final state.
deadStates :: forall s l . NFA s l -> (Bool, Set s)
deadStates (NFA lts@(LTS m) isInit isFinal) = (deads == allStates, deads)
  where
    allStates = statesLTS lts
    -- Only reachable and useful states are not dead.
    deads = allStates S.\\ (reachableStates `S.intersection` usefulStates)

    (initStates, finalStates) =
        S.foldr toInitFinal (S.empty, S.empty) allStates

    toInitFinal s (is, fs) =
        let mkInit = if isInit s then (s `S.insert`) else id
            mkFinal = if isFinal s then (s `S.insert`) else id
        in (mkInit is, mkFinal fs)

    -- If we have no finals, nothing is useful, otherwise, we obtain the states
    -- that can reach a final state.
    usefulStates = findReachable backwardSteps finalStates finalStates
    -- If we have no inits, nothing is reachable, otherwise, we obtain the
    -- states reachable from an initial states.
    reachableStates  = findReachable forwardSteps initStates initStates

    (forwardSteps, backwardSteps) = M.foldrWithKey folder inits m
      where
        inits = (M.empty, M.empty)

        folder src mtbdd = inserter src (bigUnion $ values mtbdd)
        inserter src dsts (fwds, bwds) =
            let fwds' = M.insert src dsts fwds
                insertUnionSrc d = M.insertWith S.union d (S.singleton src)
                bwds' = S.foldr insertUnionSrc bwds dsts
            in (fwds', bwds')

    -- Do a search of the NFA graph to determine which states are
    -- reachable.
    findReachable :: Map s (Set s) -> Set s -> Set s -> Set s
    findReachable oneSteps todo done
        | S.null todo = done
        | otherwise =
            let todo' = bigUnion (S.map getTargets todo) S.\\ done
                done' = done `S.union` todo'
            in findReachable oneSteps todo' done'
      where
        getTargets s = fromMaybe S.empty $ s `M.lookup` oneSteps

-- |'prune' removes transitions from an 'LTS'. Note: w.r.t. the paper "Advanced
-- Automata Minimisation" we only prune w.r.t.  P(id, <k-di) because the other
-- prune methods require to reverse the NFA, which is innefficient. 'prune'
-- takes an nfa, a rel (<k-di) and returns the pruned nfa.
-- Transitions are pruned such that (s, l, t) is in the resulting transition
-- relation only if there is no (s', l, t') such that s == s' and t `rel` t'.
prune :: (Functor m, Monad m) => LTS s l -> Rel s -> WriterT Any m (LTS s l)
prune (LTS m) rel = do
    m' <- DT.mapM (MTBDD.unaryM pruneTargets) m
    return $ LTS m'
  where
    -- Quotient tgts by rel.
    pruneTargets tgts = DF.foldrM step tgts $ S.map (id &&& (rel M.!)) tgts

    -- Use a Writer monad, to notify the caller of prune that something was
    -- changed (when we remove elements from a target set).
    step (t, trel) keeping = do
        let relatedInTgts = not . S.null $ keeping `S.intersection` trel
        if relatedInTgts
            then setFlag >> return (t `S.delete` keeping)
            else return keeping

generateSimRel :: (Ord s) => NFA s l -> Int -> Rel s
generateSimRel nfa lookahead = transitivelyCloseMap res
  where
    res = runEval . iterateWhile step $ initR
    initR = initRel nfa
    step rel = simRelStep nfa rel lookahead

simRelStep :: forall s l m . (Monad m, Applicative m) => NFA s l -> Rel s
           -> Int -> WriterT Any m (Rel s)
simRelStep (NFA (LTS trans) _ isFinal) rel lookahead =
    M.traverseWithKey refine rel
  where
    transFor = getTrans trans

    -- Take a state and the set of related states and refine the related states
    -- setting a flag if something changed.
    refine p rs
        | S.null rs = return rs
        | rs == S.singleton p = return rs
        | otherwise = do
            let rs' = rs S.\\ nonSimulatingSubset lookahead p rs
            -- Notify that something has changed.
            when (S.size rs /= S.size rs') setFlag
            return rs'

    -- Return the set of passed states that don't simulate the given state @p@
    -- with lookahead @k@.
    nonSimulatingSubset :: Int -> s -> Set s -> Set s
    nonSimulatingSubset k p = S.filter notSimulating
      where
        notSimulating r = doesNotSimulate k (S.singleton p) (S.singleton r)
            (transFor p) (transFor r)

    doesNotSimulate :: Int -> Set s -> Set s -> TransitionBDD s l
                    -> TransitionBDD s l -> Bool
    doesNotSimulate k simulatees simulating simulateeTargets simulatingTargets
        | k == 0 = True
        | simulatees == simulating = False
        | S.null simulating = True
        -- Fold over all labels: if we can't simulate at any of them, we fail.
        | otherwise = getAny $
            MTBDD.binaryFoldMap (Any .: isFailure)
                simulateeTargets simulatingTargets
      where
        toUnionTrans places
            -- Optimise lookup of BDDs we already have.
            | places == simulatees = simulateeTargets
            | places == simulating = simulatingTargets
            | otherwise = MTBDD.or . S.map transFor $ places

        -- If none of @ps@ failed, not a failure.
        isFailure ps qs = not (S.null fails) &&
            failsAfterMoreLookaheadRespectFinals fails qs
          where
            -- If p can't transition on a label (i.e. ps is empty), q trivially
            -- simulates it, and no states fail. Otherwise, fails is the set of
            -- targets of @p@ that are not related to any targets of @q@ (which
            -- is an element of the set currently related to @p@)
            fails = S.filter (S.null . S.intersection qs . (rel M.!)) ps

        -- If a particular fail is final, it can only try more lookahead
        -- with the finals in qs. Otherwise, we could build invalid
        -- traces (p_1, p_2,... p_n, q_1, q_2,... q_n) where for some i,
        -- p_i is final, but q_i is not.
        failsAfterMoreLookaheadRespectFinals fails qs
            | not (DF.any isFinal fails) = failAfterMoreLookahead fails qs
            | otherwise =
                let (failsFinal, failsNonFinal) = S.partition isFinal fails
                    (qsFinal, _) = S.partition isFinal qs
                in failAfterMoreLookahead failsFinal qsFinal ||
                   failAfterMoreLookahead failsNonFinal qs

        -- Inputs are target sets @ps@ and @qs@ (reached after taking a
        -- particularly-labelled transition), where @related(ps)@, and @qs@
        -- have no overlap. In the non-lookahead case this is failure, however,
        -- if we can ensure that each state reachable from @ps@ has a related
        -- state in those reachable from @qs@, we don't fail. Take the union of
        -- the states' transitions to consider all labels of all states at
        -- once.
        failAfterMoreLookahead ps qs =
            let pTrans = toUnionTrans ps
                qTrans = toUnionTrans qs
            in doesNotSimulate (k - 1) ps qs pTrans qTrans

-- calculate a (possible) initial relation
-- initial relation of an nfa is defined as: (na, S) U (a, A) such that
-- na is a non-accepting state, S is the subset of states that can do all the
-- actions of na. a is an accepting state, A is the subset of final states that
-- can do all the actions of a
initRel :: forall s l . NFA s l -> Rel s
initRel nfa@(NFA lts _ isFinal) =
    -- Union (na, S) rel with the (a,A) rel.
    S.fold (makeRel finals) nonFinalsRel finals
  where
    -- The (na,S) rel
    nonFinalsRel = S.fold (makeRel allStates) M.empty nonFinals

    -- all the states in the nfa
    allStates = statesLTS lts
    (finals, nonFinals) = S.partition isFinal allStates

    -- Given a set of states @S@, a state @s@ is related to the subset of @S@
    -- that can perform all the actions of @s@.
    makeRel :: Set s -> s -> Rel s -> Rel s
    makeRel states s = M.insert s (statesSimulating s states)

    -- Return the subset of the passed states that can take transitions
    -- labelled in the same way as transitions from the given state.
    statesSimulating s = S.filter (\q -> canDoAllActionsOf nfa q s)

-- Can state p do all actions of state q?
canDoAllActionsOf :: NFA s l -> s -> s -> Bool
canDoAllActionsOf (NFA (LTS trans) _ _) p q
    | p == q = True
    | otherwise =
        let pT = getTrans trans p
            qT = getTrans trans q
            -- False if x is empty and y not (i.e. p can't take a label q can).
            isMatched x y = not (S.null x) || S.null y
        in getAll $ MTBDD.binaryFoldMap (All .: isMatched) pT qT

-- Return the empty BDD if we have no such source state.
getTrans :: (Ord s, Ord l) => LTSTransitionsBDD s l -> s -> TransitionBDD s l
getTrans trans = fromMaybe (MTBDD.constant S.empty) . (`M.lookup` trans)

-- Writer helpers
setFlag :: (Monad m) => WriterT Any m ()
setFlag = tell (Any True)
