{-# LANGUAGE GADTs, StandaloneDeriving #-}
module LTS where

import MTBDD ( MTBDD, values, (||), unitWithVars )
import Control.DeepSeq ( NFData(..) )
import qualified Data.Set as S ( union, empty, singleton )
import Data.Set ( Set )
import qualified Data.Map.Strict as M ( keysSet, foldr, insertWith )
import Data.Map.Strict ( Map )

import MapSetUtils ( bigUnion )

type LTSState = Int

-- A 'LTSTransition' is a Map from States @s@, to (set-valued) MTBDDs over some
-- label component type, @l@.
type LTSTransitionsBDD s l = Map s (TransitionBDD s l)
type TransitionBDD s l = MTBDD l (Set s)

data LTS s l where
    LTS :: (Ord s, Ord l) => LTSTransitionsBDD s l -> LTS s l

deriving instance (Eq s, Eq l) => Eq (LTS s l)
deriving instance (Show s, Show l) => Show (LTS s l)

instance (NFData s) => NFData (LTS s l) where
    rnf (LTS m) = rnf m

-- | Given an LTS, extract the set of states. N.B. a state is only considered
-- to be part of an LTS if that state appears as a source or target of some
-- transition of the LTS.
statesLTS :: LTS s l -> Set s
statesLTS (LTS trans) = M.keysSet trans `S.union`
    M.foldr (\bdd -> S.union (bigUnion $ MTBDD.values bdd)) S.empty trans

addTransition :: LTS s l -> s -> [(l, Bool)] -> s -> LTS s l
addTransition (LTS transMap) src lbls tgt = LTS transMap'
  where
    transMap' = M.insertWith (MTBDD.||) src bdd transMap
    bdd = MTBDD.unitWithVars S.empty lbls (S.singleton tgt)
