{-# LANGUAGE FlexibleInstances #-}
module NetGen where

import Control.Arrow ( (&&&), (***) )
import Control.Applicative ( (<$>) )
import Control.Lens ( (%~), view )
import qualified Data.HashSet as HS
import qualified Data.IntSet as IS
import Data.List ( elemIndex, partition )
import Data.Maybe ( fromJust )
import Test.QuickCheck ( Arbitrary(..), elements, choose, vectorOf, Gen
                       , elements, suchThat, frequency )
import Marking ( markingListToList, listToMarkingList, TokenStatus(..) )
import Nets ( NetWithBoundaries(..), NetTransition(..), leftBounds, rightBounds
            , produceAts, consumeFroms, queries, isInternalTransition )

-- Only the places/boundaries mentioned in the transitions influence the size
-- of the boundaries/places - if a place/boundary isn't mentioned, we remove it
-- and rename all other places/boundaries appropriately:
--
-- NWB 3 3 [P,A,P] $ [ ({2}, {}, {}, {1}, {1}), ({0}, {0}, {}, {}, {1})]
-- ==>
-- NWB 2 1 [P,A] $ [ ({1}, {}, {}, {1}, {0}), ({0}, {0}, {}, {}, {0})]
fixUnused :: NetWithBoundaries -> NetWithBoundaries
fixUnused (NetWithBoundaries _ _ s m its ets) =
    NetWithBoundaries l' r' s m' its' ets'
  where
    (usedLs, usedPs, usedRs) =
        HS.foldr unionUsedPorts (IS.empty, IS.empty, IS.empty ) $
            its `HS.union` ets

    unionUsedPorts t (ls, ps, rs) =
        ( ls `IS.union` view leftBounds t
        , ps `IS.union` view produceAts t `IS.union`
                        view consumeFroms t `IS.union`
                        view queries t
        , rs `IS.union` view rightBounds t)

    its' = modifyTs its
    ets' = modifyTs ets

    modifyTs ts = flip HS.map ts $ \(NetTrans ls cf pa q rs _) ->
        NetTrans (IS.map newL ls) (IS.map newP cf) (IS.map newP pa)
                 (IS.map newP q) (IS.map newR rs) IS.empty
      where
        newL = indexIn usedLs
        newR = indexIn usedRs
        newP = indexIn usedPs

        indexIn is i = fromJust (i `elemIndex` IS.toAscList is)

    l' = IS.size usedLs
    r' = IS.size usedRs

    m' = listToMarkingList $
        foldr deleteUnused [] (markingListToList m `zip` [0..])
    deleteUnused (t, i) res = if i `IS.member` usedPs then t : res else res

newtype PortID = PortID Integer
               deriving Show

instance Arbitrary PortID where

instance Arbitrary NetWithBoundaries where
    arbitrary = do
        numPlaces <- choose (1 :: Int, 5)
        numLBounds <- choose (1 :: Int, 5)
        numRBounds <- choose (1 :: Int, 5)
        marking <- listToMarkingList <$>
            vectorOf numPlaces (elements [Present, Absent])
        numTransitions <- choose (1, numPlaces * 2)
        transList <- vectorOf numTransitions
            (makeArbitraryNetTransition numPlaces numLBounds numRBounds)
        let toHS = HS.fromList *** HS.fromList
            (iTrans, eTrans) = toHS . partition isInternalTransition $ transList
        return $
            NetWithBoundaries numLBounds numRBounds 0 marking iTrans eTrans

    shrink = doShrink

doShrink :: NetWithBoundaries -> [NetWithBoundaries]
doShrink (NetWithBoundaries l r s m its ets)
        | HS.null ets && HS.null its = []
        | otherwise = map (fixUnused . tsToNWB) tList'
      where
        tsToNWB = uncurry (NetWithBoundaries l r s m) .
            (HS.fromList *** HS.fromList) .  partition isInternalTransition

        tList = HS.toList its  ++ HS.toList ets
        tList' = filter (not . null) $
            removeSingleTransition tList ++ removeSinglePort tList

        removeSingleTransition xs = map (removeAt xs) [0..length xs - 1]

        removeLBoundI = removeFromISet leftBounds
        removeRBoundI = removeFromISet rightBounds
        removePlaceI i t =
            removeFromISet consumeFroms i .
            removeFromISet produceAts i .
            removeFromISet queries i $ t

        removeSinglePort xs =
            let ignoreLBound i = map (removeLBoundI i) xs
                ignoreRBound i = map (removeRBoundI i) xs
                ignorePlace i = map (removePlaceI i) xs
                toTrans ys = [ filter okTrans ys | xs /= ys]
            in concatMap toTrans $
                map ignoreLBound [0..(l - 1)] ++
                map ignoreRBound [0..(r - 1)] ++
                map ignorePlace [0..(r - 1)]

        okTrans (NetTrans ls cf pa q rs _) =
            not $ IS.null ls && IS.null cf && IS.null pa && IS.null q &&
                  IS.null rs

        removeFromISet lens i = lens %~ IS.delete i

        removeAt xs i = let (before, after) = splitAt i xs
                        in before ++ tail after

makeArbitraryNetTransition :: Int -> Int -> Int -> Gen NetTransition
makeArbitraryNetTransition numPlaces numLBounds numRBounds =
    flip suchThat nonEmpty $ do
        lbs <- chooseLBounds
        -- TODO: make sure these 3 are disjoint?
        cf <- choosePlaces IS.empty IS.empty
        pa <- choosePlaces cf IS.empty
        q <- choosePlaces cf pa
        rbs <- chooseRBounds
        return $ NetTrans lbs cf pa q rbs IS.empty
  where
    nonEmpty (NetTrans lb cf pa q rbs _) = not $ IS.null lb &&
                                                 IS.null cf &&
                                                 IS.null pa &&
                                                 IS.null q &&
                                                 IS.null rbs

    placeWeight ls rs i =
        let inls = i `IS.member` ls
            inrs = i `IS.member` rs
        in if inls && inrs
               then 1
               else if inls || inrs
                   then 2
                   else 30

    choosePredN n gen = do
        howMany <- choose(0, n)
        IS.fromList <$> vectorOf howMany gen

    choosePlaces ls rs =
        let weightedPlaces =
                map (placeWeight ls rs &&& return) [0..numPlaces-1]
        in choosePredN numPlaces (frequency weightedPlaces)

    chooseLBounds = choosePredN numLBounds (choose (0, numLBounds - 1))
    chooseRBounds = choosePredN numRBounds (choose (0, numRBounds - 1))

