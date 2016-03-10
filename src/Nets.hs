{-# OPTIONS_GHC -fno-warn-orphans #-} -- For the Hashable IntSet instance.
{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, TupleSections, TypeSynonymInstances, FlexibleInstances, DeriveGeneric, CPP #-}
module Nets where

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative ( (<$>) )
#endif

import Control.Monad ( guard )
import Control.Lens ( makeLenses, (<<%~), _1, _2, (%~) )
import Data.IntSet ( IntSet )
import qualified Data.IntSet as IS
import Data.Hashable ( Hashable(..) )
import Data.List ( intercalate )
import qualified Data.Map.Strict as M ( empty, insertWith, deleteFindMin, null
                                      , unionWith )
import Data.Maybe ( fromMaybe, mapMaybe )
import Data.Number.Nat ( toNat )
import Data.Set ( Set )
import Data.Text ( pack )
import qualified Data.Set as S ( union, empty, null, intersection, fromList
                               , singleton, minView, toList )
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import GHC.Generics ( Generic )
import Prelude hiding ( minBound )
import Marking ( WildCardMarking, Marking, concatMarkingList, sizeMarkingList
               , TokenStatus(Present), markingListToList, listToMarkingList )

import LOLANets ( LOLANet(..) )
import PEPParser ( LLNet(..), Place(..), Transition(..), Header(..)
                 , Position(..), InfinityOrNum(Number), LLNetType(PTNet)
                 , FormatType(N2), ObjectData(..), Arc(..), ArcType(..)
                 , PlaceAttribute(PlaceInitialMarking, PlaceCapacity)
                 , PlaceAttribute(PlaceInitialMarking), PlaceID(..)
                 , TransID(..) )
import Util ( (.:), Pretty(..), indentLines )

data PortType = LeftBoundary
              | RightBoundary
              | ProduceAt
              | ConsumeFrom
              | Query
              deriving (Eq, Ord, Show)

isPlace :: PortType -> Bool
isPlace ProduceAt = True
isPlace ConsumeFrom = True
isPlace Query = True
isPlace _ = False

-- A NetTransition represents the set of ports the transition connects. For
-- efficiency, we partition the ports based on their types.
data NetTransition = NetTrans
                         { _leftBounds :: !IntSet
                         , _consumeFroms :: !IntSet
                         , _produceAts :: !IntSet
                         , _queries :: !IntSet
                         , _rightBounds :: !IntSet
                         , _syncs :: !IntSet
                         }
                   deriving ( Generic, Ord, Eq, Show )

$(makeLenses ''NetTransition)

-- This is an orphan instance, but we need it to be able to hash NetTransitions
instance Hashable IntSet where
    hashWithSalt s is = hashWithSalt s $ IS.toList is

instance Hashable NetTransition

instance Pretty NetTransition where
    pretty (NetTrans ls cf pa q rb s) = wrap $
        intercalate "\t" [ prettyIS ls
                         , prettyIS cf
                         , prettyIS pa
                         , prettyIS q
                         , prettyIS rb
                         , prettyIS s
                         ]
      where
        prettyIS = wrap . intercalate "," . map show . IS.toList
        wrap = ("{" ++) . (++ "}")

-- Point-wise union two transitions, ensuring that the transitions are not in
-- direct contention (i.e. connected to the same port)
unionNetTransition :: NetTransition -> NetTransition -> NetTransition
unionNetTransition t1@(NetTrans llb lcf lpa lq lrb ls)
                   t2@(NetTrans rlb rcf rpa rq rrb rs)
    | t1 `inContention` t2 =
        error $ "Attempting to union transitions in contention!\n"
                    ++ show t1 ++ "\n" ++ show t2
    | otherwise = NetTrans lb cf pa q rb s
  where
    lb = llb `IS.union` rlb
    cf = lcf `IS.union` rcf
    pa = lpa `IS.union` rpa
    q = lq `IS.union` rq
    rb = lrb `IS.union` rrb
    s = ls `IS.union` rs

inContention :: NetTransition -> NetTransition -> Bool
inContention (NetTrans llb lcf lpa lq lrb ls)
             (NetTrans rlb rcf rpa rq rrb rs) =
    nonEmptyISIntersection ls rs ||
    nonEmptyISIntersection llb rlb ||
    nonEmptyISIntersection lrb rrb ||
    -- Check if there is any overlap between place ports other than both
    -- querying the same port.
    nonEmptyISIntersection lcf rcf ||
    nonEmptyISIntersection lpa rcf ||
    nonEmptyISIntersection lcf rpa ||
    nonEmptyISIntersection lpa rpa ||
    nonEmptyISIntersection lcf rq ||
    nonEmptyISIntersection lpa rq ||
    nonEmptyISIntersection lq rcf ||
    nonEmptyISIntersection lq rpa

selfConflicting :: NetTransition -> Bool
selfConflicting (NetTrans _ consume produce query _ _) =
        nonEmptyISIntersection consume produce ||
        nonEmptyISIntersection consume query ||
        nonEmptyISIntersection produce query

nonEmptyISIntersection :: IntSet -> IntSet -> Bool
nonEmptyISIntersection = not . IS.null .: IS.intersection

emptyNetTransition :: NetTransition
emptyNetTransition =
    NetTrans IS.empty IS.empty IS.empty IS.empty IS.empty IS.empty

nullNetTransition :: NetTransition -> Bool
nullNetTransition = (== emptyNetTransition)

-- TODO: track set of conflicting transitions
-- The marking encodes the number of states in the net.
data NetWithBoundaries =
    NetWithBoundaries !Int                 -- ^ Left boundary count
                      !Int                 -- ^ Right boundary count
                      !Int                 -- ^ Hidden boundary count
                      !Marking             -- ^ Which places are marked?
                      !(HashSet NetTransition) -- ^ Set of Internal Transitions
                      !(HashSet NetTransition) -- ^ Set of Transitions
    deriving (Eq, Ord, Show)

-- TODO: this is stupid, we shouldn't ever need to order nets.
instance Ord (HashSet NetTransition) where
    hs1 <= hs2 = HS.toList hs1 <= HS.toList hs2

instance Pretty NetWithBoundaries where
    pretty (NetWithBoundaries l r s m ti te) =
        "NWB: " ++ show (l, r, s) ++ " " ++ pretty m ++"\n"
            ++ indentLines ("Internal: " : map pretty (HS.toList ti)
                ++ ["External: "] ++ map pretty (HS.toList te))

type MarkedNet = (WildCardMarking, NetWithBoundaries)

shiftTrans :: Int -> Int -> Int -> Int -> NetTransition -> NetTransition
shiftTrans lOffset pOffset rOffset sOffset (NetTrans lb cf pa q rb s) =
    NetTrans lb' cf' pa' q' rb' s'
  where
    lb' = IS.map (+ lOffset) lb
    cf' = IS.map (+ pOffset) cf
    pa' = IS.map (+ pOffset) pa
    q' = IS.map (+ pOffset) q
    rb' = IS.map (+ rOffset) rb
    s' = IS.map (+ sOffset) s

-- An internal transition is one that is not connected to any boundary ports.
isInternalTransition :: NetTransition -> Bool
isInternalTransition (NetTrans lb _ _ _ rb _) = IS.null lb && IS.null rb

-- Union together the transitions (and underlying places) by offsetting the
-- smaller set of places by the size of the larger set. The resulting net is
-- isomorphic whichever we choose, so it doesn't matter.
composePreProcess :: MarkedNet -> MarkedNet
                  -> Maybe ( WildCardMarking, Marking
                           , NetWithBoundaries, NetWithBoundaries)
composePreProcess (lwm, lNet@(NetWithBoundaries _ lr ls lm _ _))
                  (rwm, rNet@(NetWithBoundaries rl _ rs rm _ _)) = do
        guard (lr == rl)
        return $ if lPlaceCount > rPlaceCount
            then ( lwm `concatMarkingList` rwm
                 , lm `concatMarkingList` rm
                 , lNet, offsetPlacesSyncsBy lPlaceCount ls rNet)
            else ( rwm `concatMarkingList` lwm
                 , rm `concatMarkingList` lm
                 , offsetPlacesSyncsBy rPlaceCount rs lNet, rNet)
  where
    lPlaceCount = sizeMarkingList lm
    rPlaceCount = sizeMarkingList rm

    offsetPlacesSyncsBy pOffset sOffset (NetWithBoundaries l r h m it et) =
        NetWithBoundaries l r h m (shiftPlaces it) (shiftPlaces et)
      where
        shiftPlaces = HS.map (shiftTrans 0 pOffset 0 sOffset)

data ConnectionType = Unconnected
                    | Connected

classifyConnection :: NetTransition -> ConnectionType
classifyConnection (NetTrans lb _ _ _ rb _)
    | IS.null lb && IS.null rb = Unconnected
    | otherwise = Connected

partitionConnections :: [NetTransition] -> ([NetTransition], [NetTransition])
partitionConnections = foldr insertConnection ([],[])

insertConnection :: NetTransition -> ([NetTransition], [NetTransition])
                 -> ([NetTransition], [NetTransition])
insertConnection nt partition = case classifyConnection nt of
    Unconnected -> consTrans _1
    Connected -> consTrans _2
  where
    consTrans lens = lens %~ (nt :) $ partition

compose :: NetWithBoundaries -> NetWithBoundaries -> Maybe NetWithBoundaries
compose n1 n2 =
    -- Implement in terms of markednet composition with empty markings
    snd <$> composeMarkedNet (withMark n1) (withMark n2)
  where
    withMark = (listToMarkingList [], )

composeMarkedNet :: MarkedNet -> MarkedNet -> Maybe MarkedNet
composeMarkedNet = (composeMarkedNet' <$>) .: composePreProcess
  where
    composeMarkedNet'
        ( wcMarking
        , marking
        , NetWithBoundaries llCount lrCount lHidden _ liTrans leTrans
        , NetWithBoundaries _ rrCount rHidden _ riTrans reTrans
        ) = (wcMarking, newNet)
      where
        newNet = NetWithBoundaries llCount rrCount hidden marking iTrans eTrans
        hiddenBase = lHidden + rHidden
        hidden = hiddenBase + lrCount

        iTrans = HS.fromList ucProcessed `HS.union` liTrans `HS.union` riTrans
        eTrans = HS.fromList cProcessed `HS.union` HS.fromList lrUnconnected

        -- As transitions become totally unconnected to boundary ports, we want
        -- to ignore them when performing future net compositions (they play no
        -- part in synchronisations, and can simply be unioned).
        (ucProcessed, cProcessed) = processSyncTransMap ([], []) lrSyncMap

        -- The SyncTrans map is a map from shared boundary ports to the
        -- SyncTrans that are syncing on that port. We process the shared
        -- boundary ports in order, merging transitions that sync on a common
        -- port.
        processSyncTransMap completed todo
            | M.null todo = completed
            | otherwise =
                -- If either Set is empty, there is are transitions that are
                -- connected to a particular boundary port on one side, but no
                -- transitions with which they can sync, so we discard them
                -- all.
                if null lSyncs || null rSyncs
                    then processSyncTransMap completed todo'
                    else processSyncTransMap completedAdded todoAdded
              where
                ((_, (lSyncs, rSyncs)), todo') = M.deleteFindMin todo

                completedAdded = newCompletes `concatPairs` completed
                concatPairs (xs, ys) (zs, ws) = (xs ++ zs, ys ++ ws)
                todoAdded = M.unionWith concatPair newTodos todo'

                (newCompletes, newTodos) =
                    foldr processResult (([], []), M.empty) unionedSyncs

                -- We may end up with "empty" transitions, so ignore them, e.g.
                -- connecting two simple wiring-only loops to each other,
                -- closing the loop.
                processResult (Done nt) origRes
                    | nullNetTransition nt = origRes
                    | otherwise = _1 %~ insertConnection nt $ origRes
                processResult (NotDone i syncOnSide st) (c, t) =
                    let stPair = case syncOnSide of
                                     SyncOnL -> ([st], [])
                                     SyncOnR -> ([], [st])
                    in (c, M.insertWith concatPair i stPair t)

                unionedSyncs = foldr doUnionSync [] rSyncs
                doUnionSync rSync done =
                    mapMaybe (unionSync rSync) lSyncs ++ done

        -- Take two SyncTrans and merge them, or, if there is nothing left to
        -- sync on, return the resulting transition.
        unionSync (SyncTrans otherLL otherRL syncedOnL restLL restRL)
                  (SyncTrans otherLR otherRR syncedOnR restLR restRR) = do
            -- Contention in either underlying net
            guardNot $ restLL `inContention` restLR
            guardNot $ restRL `inContention` restRR
            -- Trying to sync on equal ports
            guardNot $ otherLL `intersectsWith` otherLR
            guardNot $ otherRL `intersectsWith` otherRR
            -- Previously synced on the same boundary port == contention
            guardNot $ not . S.null $ syncedOnL `S.intersection` syncedOnR
            case findNextSync otherL otherR of
                Nothing ->
                    let toSync = (+ hiddenBase) . fst
                        syncPortIDs = IS.fromList . map toSync . S.toList $
                            syncedOns
                        -- We know restsL and restsR aren't in contention,
                        -- since they connect to disjoint places/boundaries.
                        rest = restsL `unionNetTransition` restsR
                    in return . Done $ syncs %~ IS.union syncPortIDs $ rest
                Just (syncBoundary, syncSide, otherL', otherR') ->
                    return . NotDone syncBoundary syncSide $
                        SyncTrans otherL' otherR' syncedOns restsL restsR
          where
            guardNot = guard . not
            syncedOns = syncedOnL `S.union` syncedOnR
            restsL = restLL `unionNetTransition` restLR
            restsR = restRL `unionNetTransition` restRR
            intersectsWith :: (Ord a) => Set a -> Set a -> Bool
            intersectsWith = not . S.null .: S.intersection
            otherL = otherLL `S.union` otherLR
            otherR = otherRL `S.union` otherRR

        -- Try and find the next Sync. We cancel mutually synced syncs (i.e. if
        -- a transition needs to sync on L2 and R2, it must've been formed of
        -- two transitions that also connected to these boundaries, so we can
        -- ignore them - it syncs with itself), until we find an unmatched
        -- boundary sync (or if nothing, we're done).
        findNextSync l r = case (S.minView l, S.minView r) of
            (Nothing, Nothing) -> Nothing
            (Just (minL, restL), Nothing) ->
                Just (unLeftSync minL, SyncOnL, restL, S.empty)
            (Nothing, Just (minR, restR)) ->
                Just (unRightSync minR, SyncOnR, S.empty, restR)
            (Just (minL, restL), Just (minR, restR)) ->
                let minL' = unLeftSync minL
                    minR' = unRightSync minR
                in case compare minL' minR' of
                    LT -> Just (minL', SyncOnL, restL, r)
                    EQ -> findNextSync restL restR
                    GT -> Just (minR', SyncOnR, l, restR)

        -- Generate the initial SyncMap. This is a map that maps boundary ports
        -- to transitions, such that a transition is in the entry for its
        -- minimal boundary port connection (if any). If a transition is not
        -- connected to a boundary port, it is inserted into the unsync set.
        lres = foldr (insertSync True) ([], M.empty) $ HS.toList leTrans
        (lrUnconnected, lrSyncMap) =
            foldr (insertSync False) lres $ HS.toList reTrans

        concatPair (x, y) (z, w) = (x ++ z, y ++ w)

        -- insertSync generates the SyncTrans for a transition, and inserts it
        -- into the map. isLeft is True if this transition is on the left side
        -- of a composition.
        insertSync isLeft t (unconnected, connectedMap)
            | IS.null sharedBounds = (t : unconnected, connectedMap)
            | otherwise =
                let (minBound, otherBounds) = IS.deleteFindMin sharedBounds
                    side = if isLeft then SyncOnL else SyncOnR
                    st = [toSyncTrans minBound side otherBounds]
                    pair = if isLeft
                               then (st, [])
                               else ([], st)
                    connectedMap' =
                        M.insertWith concatPair minBound pair connectedMap
                in (unconnected, connectedMap')
          where
            (sharedBounds, rest) =
                let lens = if isLeft then rightBounds else leftBounds
                -- Modify the appropriate lens, returning the old value
                in (lens <<%~ const IS.empty) t

            toSyncTrans minB side others =
                let mkLeftRight =
                        if isLeft
                            then (, S.empty) . S.fromList . map LeftSync
                            else (S.empty, ) . S.fromList . map RightSync
                    (lSyncs, rSyncs) = mkLeftRight $ IS.toAscList others
                    (lRest, rRest) = if isLeft
                                         then (rest, emptyNetTransition)
                                         else (emptyNetTransition, rest)
                in SyncTrans lSyncs rSyncs (S.singleton (minB, side)) lRest rRest

data SyncUnionResult = Done !NetTransition
                     | NotDone !Int !SyncOnSide !SyncTrans
                     deriving ( Show )

type BoundarySync = (Int, SyncOnSide)

newtype LeftSync = LeftSync { unLeftSync :: Int }
                 deriving (Eq, Ord, Show)
newtype RightSync = RightSync { unRightSync :: Int }
                  deriving (Eq, Ord, Show)

data SyncTrans = SyncTrans !(Set LeftSync)     -- ^ Ports to sync on left
                           !(Set RightSync)    -- ^ Ports to sync on right
                           !(Set BoundarySync) -- ^ Ports that were synced on
                           !NetTransition      -- ^ Other ports on left
                           !NetTransition      -- ^ Other ports on right
               deriving ( Show )

data SyncOnSide = SyncOnL
                | SyncOnR
                deriving ( Eq, Ord, Show )

tensor :: NetWithBoundaries -> NetWithBoundaries -> NetWithBoundaries
tensor (NetWithBoundaries llCount lrCount lSynced lMarking liTrans leTrans)
       (NetWithBoundaries rlCount rrCount rSynced rMarking riTrans reTrans) =
        NetWithBoundaries lCount rCount synced marking iTrans eTrans
  where
    synced = lSynced + rSynced
    lCount = llCount + rlCount
    rCount = lrCount + rrCount
    marking = lMarking `concatMarkingList` rMarking

    doOffset = HS.map (shiftTrans llCount lNumPlaces lrCount lSynced)

    lNumPlaces = sizeMarkingList lMarking
    -- TODO: use same optimisation as compose - offset the smaller net?
    iTrans = liTrans `HS.union` doOffset riTrans
    -- Offset the left/right boundary ports by the left/right boundary counts
    -- in the left net.
    eTrans = leTrans `HS.union` doOffset reTrans

net2LOLANet :: NetWithBoundaries -> LOLANet
net2LOLANet (NetWithBoundaries lCount rCount _ marking iTrans eTrans) =
    LOLANet allPlaces mark trans
  where
    placeCount = sizeMarkingList marking

    (places, mark) = foldr makePlacesMarking ([], []) $
        zip [0..placeCount] (markingListToList marking)

    makePlacesMarking (i, tok) (ps, ms) =
        let p = toPlace i in
        (p : ps, (if tok == Present then (p :) else id) ms)

    allPlaces = places ++ boundaries
    -- Create extra places for each boundary port.
    boundaries = toBoundaries True [0..lCount - 1] ++
                 toBoundaries False [lCount..lCount + rCount - 1]

    trans = zipWith (curry toTrans) [(0 :: Int)..] $
        HS.toList iTrans ++ HS.toList eTrans

    toTrans (i, NetTrans lb cf pa q rb _)
        | not $ IS.null q = error "Query ports not supported by LOLANet format"
        | otherwise = ('T' : show i, lb' ++ rb' ++ cf', pa')
      where
        lb' = map (("BL" ++) . show) $ IS.toAscList lb
        rb' = map (("BR" ++) . show) $ IS.toAscList rb
        cf' = map toPlace $ IS.toAscList cf
        pa' = map toPlace $ IS.toAscList pa

    toPlace = ("P" ++) . show

    toBoundaries isLeft = map $ \i ->
        'B' : if isLeft then 'L' : show i else 'R' : show (i - lCount)

net2LLNet :: NetWithBoundaries -> LLNet
net2LLNet = errorIfReadArcs . net2LLNetWithReadArcs
  where
    errorIfReadArcs (LLNetWithReadArcs llNet []) = llNet
    errorIfReadArcs (LLNetWithReadArcs _ _) =
        error "Query ports not supported by LLNet format"

data LLNetWithReadArcs = LLNetWithReadArcs LLNet [(TransID, PlaceID)]

net2LLNetWithReadArcs :: NetWithBoundaries -> LLNetWithReadArcs
net2LLNetWithReadArcs
    (NetWithBoundaries lCount rCount _ marking iTrans eTrans) =
        LLNetWithReadArcs llNet readArcs
  where
    llNet = LLNet header defaults blocks allPlaces trans pTrans arcs textLines
    placeCount = sizeMarkingList marking

    header = Header PTNet N2
    defaults = []
    blocks = []
    places = zipWith (curry toPlace)
        [1..placeCount] (markingListToList marking)
    allPlaces = places ++ boundaries
    -- Create extra places for each boundary port.
    boundaries = toBoundaries placeCount True [1..lCount] ++
                 toBoundaries placeCount False [lCount + 1..lCount + rCount]
    pTrans = []
    textLines = []

    (trans, arcs, readArcs) = foldr toTransArcs ([], [], []) . zip [1..] $
        HS.toList iTrans ++ HS.toList eTrans

    toTransArcs (i, NetTrans lb cf pa q rb _) ~(ts, as, ras) =
        ( Transition (mkObjData i "t" Nothing) [] : ts
        , newArcs ++ as
        , newReadArcs ++ ras
        )
      where
        lb' = IS.toAscList lb
        rb' = IS.toAscList rb
        cf' = IS.toAscList cf
        pa' = IS.toAscList pa
        q' = IS.toAscList q

        newReadArcs = map ((tid,) . toPID) q'

        newArcs = map (\at -> Arc at []) $
            map (TPArc tid . toBID True) lb'
            ++
            map (flip PTArc tid . toPID) cf'
            ++
            map (TPArc tid . toPID) pa'
            ++
            map (TPArc tid . toBID False) rb'

        -- We zip with 1.. so TransIDs are already 1-indexed
        tid = TransID i

        -- We are 1-indexed in the LLNet, but 0-indexed in our Nets, so add 1.
        toBID isLeft index = PlaceID $
            1 + index + placeCount + (if isLeft then 0 else lCount)

        toPID = PlaceID . (1 +)

    toPlace (i, ts) = Place (mkObjData i "p" Nothing)
                        [ PlaceInitialMarking (ts == Present)
                        , PlaceCapacity (Number (toNat (1 :: Int)))
                        ]

    toBoundaries pSize isLeft = map toBoundary
      where
        name i = if isLeft then 'L' : show i else 'R' : show (i - lCount)
        toBoundary i =
            Place
                (mkObjData (fromIntegral $ pSize + i) "b" (Just $ name i))
                [ PlaceInitialMarking False
                , PlaceCapacity (Number (toNat (1 :: Int)))
                ]
    mkObjData i prefix mbName =
        let name = prefix ++ fromMaybe (show i) mbName
        in ObjectData (Just (Left (i, pack name))) (Position (0, 0))
