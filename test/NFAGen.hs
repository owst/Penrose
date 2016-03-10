{-# OPTIONS_GHC -fno-warn-orphans #-} -- For the Arbitrary NFA instance.
{-# LANGUAGE FlexibleInstances #-}
module NFAGen where

import Data.List ( genericReplicate )
import Data.List.NonEmpty ( NonEmpty(..), fromList )
import qualified Data.Set as S
import Test.QuickCheck ( Arbitrary(..), elements, choose )
import qualified Data.Traversable as DT
import NFA ( NFA(..) )
import ParseNFA ( ZOS(..), NFADef(..), NFATransDef(..), defToNFA )
import Util ( (.:) )

instance Arbitrary (NFA Int Int) where
    arbitrary = do
        numStates <- choose (1 :: Int, 5)
        let states = [0..numStates - 1]
        labelLength <- choose (1 :: Int, 3)
        let labels = DT.sequenceA $
                        genericReplicate labelLength [Zero, One, Star]
            allTrans = do
                s <- states
                t <- states
                l <- labels
                return (s, l, t)
        transCount <- choose (numStates, numStates * 2)
        let genericReplicateM = sequence .: genericReplicate
        trans <- genericReplicateM transCount (elements allTrans)
        initState <- elements states
        numFinal <- choose (0, numStates)
        -- not ideal, since it can pick the same state each time, but oh well
        finalStates <- genericReplicateM numFinal (elements states)
        let toNEL x = x :| []
            fudgeTran (s, l, t) = NFATransDef (toNEL s) (toNEL l) (toNEL t)
            selfLoopOn s = (s, genericReplicate labelLength Zero, s)
            supplementWithSelfLoops tr@(s, _, t) =
                [tr, selfLoopOn s, selfLoopOn t]
            withSelfLoops = trans >>= supplementWithSelfLoops
            uniqs = S.toList . S.fromList
            nelTrans = fromList . map fudgeTran . uniqs $ withSelfLoops
        return . defToNFA $ NFADef (toNEL initState) nelTrans finalStates

