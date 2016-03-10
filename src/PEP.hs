{-# LANGUAGE CPP #-}
module PEP
    ( pep2Net
    , unparseLLNet
    , llNet2Dot
    , llNet2PNML
    ) where

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative ( (<$>) )
#endif

import Control.Arrow ( (&&&), (***) )
import Control.Lens ( (^.), to, (%~), view )
import Control.Monad ( forM_, unless )
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.State.Strict ( StateT, execStateT, gets, modify )
import Data.Foldable ( foldrM )
import Data.Function ( on )
import qualified Data.IntMap as IM
import Data.IntSet ( IntSet )
import qualified Data.IntSet as IS
import qualified Data.HashSet as HS
import qualified Data.Set as S
import Data.List ( sortBy, intercalate )
import Data.Text ( pack, unpack )
import Text.XML.Light ( ppElement, node, unqual, Content(..), Attr(..)
                      , add_attr, CData(..), CDataKind(CDataRaw), xml_header )

import MapSetUtils ( renumberSet )
import Marking ( TokenStatus(..), listToMarkingList, WildCardMarking
               , WildCardMarks(..), markingListToList )
import Nets ( NetWithBoundaries(..), PortType(..), unionNetTransition
            , NetTransition(..) )
import PEPParser ( pData, ptData, objIDName, pAttributes, tData, LLNet(..)
                 , Header(..), Position(..), PlaceAttribute(..)
                 , InfinityOrNum(..), Place(..), Transition(..)
                 , ObjectData(..), PlaceAttribute(PlaceInitialMarking), Arc(..)
                 , ArcType(..), PlaceID(..), TransID(..), PTransID(..) )
import Util ( unlines )

import Prelude hiding ( unlines )

pep2Net :: LLNet -> Either String NetWithBoundaries
pep2Net (LLNet _ _ _ ps ts pts arcs _) = do
    let ps' = resolveIDs pData ps
    let ts' = resolveIDs tData ts
    let pts' = resolveIDs ptData pts
    placeSet <- execStateT (checkForDupsInIDs "place" getPID ps') IS.empty
    -- Convert from IntSet to Set (yuck!)
    let renumberer = renumberSet . S.fromList . IS.toList $ placeSet
        placeMap = IM.fromSet renumberer placeSet
        getPlaceID = (placeMap IM.!)
        -- Construct a Marking ordered by the place ids assigned.
        marking = listToMarkingList . map snd . sortBy (compare `on` fst) $
            map (renumberer . getPID &&& toTokenStatus . isInitiallyMarked) ps'
    transSet <-
        execStateT (checkForDupsInIDs "trans" getTID ts') IS.empty
    pTransSet <-
        execStateT (checkForDupsInIDs "ptrans" getPTID pts') IS.empty
    trans <- createTransSet placeSet getPlaceID transSet pTransSet
    return $ NetWithBoundaries 0 0 0 marking trans HS.empty
  where
    getODID = objIDName.to extractID

    -- Object Data has optional names and ids, at this point, we should have
    -- resolved any optional names, so these errors should never occur.
    extractID Nothing = error "PEP no ID"
    extractID (Just (Right n)) = error $ "PEP no ID, but named: " ++ show n
    extractID (Just (Left (i, _))) = i

    getPID = view (pData.getODID)
    getPTID = view (ptData.getODID)
    getTID = view (tData.getODID)

    toTokenStatus :: Bool -> TokenStatus
    toTokenStatus True = Present
    toTokenStatus False = Absent

    resolveIDs _ [] = []
    resolveIDs accessData ids = zipWith renumber [1..] ids
      where
        renumber tid thing =
            accessData.objIDName %~ doRenumber tid $ thing

        doRenumber tid Nothing = Just (Left (tid, pack $ "THING:" ++ show tid))
        doRenumber tid (Just (Right n)) = Just (Left (tid, n))
        doRenumber _ x@(Just (Left _)) = x


    isInitiallyMarked p = p ^. pAttributes . to isMarked
      where
        isMarked = (PlaceInitialMarking True `elem`)

    checkForDupsInIDs :: String -> (t -> Int) -> [t]
                    -> StateT IntSet (Either String) ()
    checkForDupsInIDs whatIsIt getID things = forM_ things $ \thing -> do
        let thingId = getID thing
        exists <- gets (thingId `IS.member`)
        if exists
            then lift . Left $
                "Duplicate " ++ whatIsIt ++ " id: " ++ show thingId
            else modify (thingId `IS.insert`)

    diag f = f *** f
    toSet = uncurry HS.union . diag (HS.fromList . IM.elems)

    createTransSet pIDs getNormPID tIDs pTIDs =
        toSet <$> foldrM addArc (IM.empty, IM.empty) arcs
      where
        -- Maintain a pair of maps, one for normal transitions and one for
        -- phantom transitions. For each arc, we have a place and a transition;
        -- insert the port corresponding to the place into the map
        -- corresponding to the transition. At the end, we'll union the values
        -- in the two maps, since we don't in general distinguish
        -- normal/phantom transitions (they might share IDs, so we do here).
        addArc (Arc arcType _attrs) (trans, pTrans) = do
            let doInsert tid pid ptype =
                    IM.insertWith unionNetTransition tid (mkSingPort pid ptype)
                checkID name valids theId =
                    unless (theId `IS.member` valids) $
                        Left $ "Unknown " ++ name ++ " : " ++ show theId
                checkNormPID pid = do
                    checkID "place" pIDs pid
                    return $ getNormPID pid
                checkTID = checkID "trans" tIDs
                checkPTID = checkID "ptrans" pTIDs
            case arcType of
                (PTArc (PlaceID pid) (TransID tid)) -> do
                    normPID <- checkNormPID pid
                    checkTID tid
                    return (doInsert tid normPID ConsumeFrom trans, pTrans)
                (TPArc (TransID tid) (PlaceID pid)) -> do
                    normPID <- checkNormPID pid
                    checkTID tid
                    return (doInsert tid normPID ProduceAt trans, pTrans)
                (PPTArc (PlaceID pid) (PTransID tid)) -> do
                    normPID <- checkNormPID pid
                    checkPTID tid
                    return (trans, doInsert tid normPID ConsumeFrom pTrans)
                (PTPArc (PTransID tid) (PlaceID pid)) -> do
                    normPID <- checkNormPID pid
                    checkPTID tid
                    return (trans, doInsert tid normPID ProduceAt pTrans)

        mkSingPort pid ptype =
            NetTrans IS.empty cf pa IS.empty IS.empty IS.empty
          where
            pSing = IS.singleton pid
            (cf, pa) = case ptype of
                           ConsumeFrom -> (pSing, IS.empty)
                           ProduceAt -> (IS.empty, pSing)
                           _ -> error $ "LLNet shouldn't generate " ++
                                        "Boundary/Query ports"

toCSV :: [String] -> String
toCSV = intercalate ", "

toPlaceName :: Int -> String
toPlaceName = ('p' :) . show

toMarkCount :: WildCardMarks -> String
toMarkCount Yes = "1"
toMarkCount No = "0"
toMarkCount _ = error "Can't handle DontCare using reachability"

markingStr :: WildCardMarking -> String
markingStr m = toCSV . map (joinWordPair . (toMarkCount *** toPlaceName)) . caredAboutPlaces $ m

joinWordPair :: (String, String) -> String
joinWordPair (w1, w2) = w1 ++ " " ++ w2

caredAboutPlaces :: WildCardMarking -> [(WildCardMarks, Int)]
caredAboutPlaces m = filter ((/= DontCare) . fst) $
        zip (markingListToList m) [(1 :: Int)..]

-- For now we only unparse the LLNet features that our net2LLNet code uses.
-- TODO: implement all LLNet features.
unparseLLNet :: WildCardMarking -> LLNet -> String
unparseLLNet marking (LLNet header _ _ places trans _ arcs _) =
    unlines [ "PEP"
            , show netType
            , show format
            , "PL"
            , unlines $ map toPlaceStr places
            , "TR"
            , unlines $ map toTransStr trans
            , "TP"
            , unlines transPlaceStrs
            , "PT"
            , unlines placeTransStrs
            , markingStr marking
            ]
  where
    (Header netType format) = header

    (transPlaceStrs, placeTransStrs) = foldr toArcStr ([],[]) arcs

    toArcStr (Arc (TPArc (TransID i) (PlaceID j)) _) ~(tps, pts) =
        ((show i ++ "<" ++ show j) : tps, pts)
    toArcStr (Arc (PTArc (PlaceID i) (TransID j)) _) ~(tps, pts) =
        (tps, (show i ++ ">" ++ show j) : pts)
    toArcStr _ _ = error "TODO: implement full unparseLLNet for arcs"

    showPos (Position (i, j)) = show i ++ "@" ++ show j

    toPlaceStr (Place (ObjectData (Just (Left (i, n))) pos)
        [ PlaceInitialMarking isMarked
        , PlaceCapacity (Number c)
        ]) = showObjData i n pos ++ concat [ "M"
                                           , if isMarked then "1" else "0"
                                           , "k"
                                           , show c
                                           ]
    toPlaceStr _ = error "TODO: implement full unparseLLNet for places"

    toTransStr (Transition (ObjectData (Just (Left (i, n))) pos) []) =
        showObjData i n pos
    toTransStr _ = error "TODO: implement full unparseLLNet for transitions"

    showObjData i n pos = concat [show i, "\"", unpack n, "\"", showPos pos]

llNet2Dot :: WildCardMarking -> LLNet -> String
llNet2Dot _ (LLNet _ _ _ places trans _ arcs _) =
    unlines [ "digraph SomeName {"
            , "node [shape = circle];"
            , unlines $ map outputPlace places
            , "node [style=filled,fillcolor=grey82,shape = box];"
            , unlines $ map outputTran trans
            , unlines $ map outputArc arcs
            , "}"
            ]
  where
    showTID i = 't': show i
    showPID i = 'p': show i

    outputPlace (Place (ObjectData (Just (Left (i, n))) _)
        [PlaceInitialMarking isMarked, _]) =
            unwords [ showPID i
                    , '[' : (if isMarked then " color=blue" else "")
                    , "label=\"" ++ unpack n ++ "\""
                    , "];"
                    ]
    outputPlace _ = error "TODO: implment full llNet2Dot for place"

    outputTran (Transition (ObjectData (Just (Left (i, n))) _) []) =
            unwords [showTID i, "[label=\"" ++ unpack n ++ "\"];"]
    outputTran _ = error "TODO: implment full llNet2Dot for tran"

    outputArc (Arc arctype _) = unwords [show s, "->", show t, ";"]
      where
        (s, t) = case arctype of
                    (TPArc (TransID i) (PlaceID j)) -> (showTID i, showPID j)
                    (PTArc (PlaceID i) (TransID j)) -> (showPID i, showTID j)
                    at -> error $ "TODO: implment full llNet2Dot for arc: "
                                    ++ show at

llNet2PNML :: WildCardMarking -> LLNet -> String
llNet2PNML marking (LLNet _ _ _ places trans _ arcs _) =
    unlines [ xml_header
            , ppElement pnmlNode
            , markingStr marking
            ]
  where
    nsAttr = Attr (unqual "xmlns")
        "http://www.pnml.org/version-2009/grammar/pnml"
    pnmlNode = add_attr nsAttr $ node (unqual "pnml") ([netNode] :: [Content])

    showTID i = 't': show i
    showPID i = 'p': show i

    netTypeAttr = Attr (unqual "type") "P/T net"

    netNode = elemWithId "SomeNetName" . add_attr netTypeAttr $
        node (unqual "net") $ childrenNode


    childrenNode = node (unqual "page") $
        map outputPlace places ++ map outputTran trans ++ map outputArc arcs


    elemWithId i = Elem . add_attr (Attr (unqual "id") i)
    textNode s = [node (unqual "text") [Text $ CData CDataRaw s Nothing]]
    withAttr an av = add_attr (Attr (unqual an) av)
    mkNode n = node (unqual n)

    outputPlace (Place (ObjectData (Just (Left (i, n))) _)
        [PlaceInitialMarking isMarked, _]) = elemWithId (showPID i) $
            node (unqual "place")
                [ mkNode "initialMarking" $
                    textNode (show $ if isMarked then 1 :: Int else 0)
                , mkNode "name" $ textNode (unpack n)
                ]
    outputPlace _ = error "TODO: implment full llNet2PNML for place"

    outputTran (Transition (ObjectData (Just (Left (i, n))) _) []) =
        elemWithId (showTID i) $ node (unqual "transition")
            [ mkNode "name" $ textNode (unpack n)
            ]
    outputTran _ = error "TODO: implment full llNet2PNML for tran"

    outputArc (Arc arctype _) =
        elemWithId name . withAttr "source" s . withAttr "target" t $
            mkNode "arc" $
                [ withAttr "value" "normal" $ mkNode "type" ()
                ]
      where
        name = s ++ " to " ++ t
        (s, t) = case arctype of
                    (TPArc (TransID i) (PlaceID j)) -> (showTID i, showPID j)
                    (PTArc (PlaceID i) (TransID j)) -> (showPID i, showTID j)
                    at -> error $ "TODO: implment full llNet2PNML for arc: "
                                    ++ show at
