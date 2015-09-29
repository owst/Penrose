{-# LANGUAGE OverloadedStrings, TupleSections, LambdaCase #-}
module DSL.ProcessParse
    ( lookupNames
    , netDefinitionToMarkedNet
    ) where
import Control.Applicative ( (<$>), (<*>) )
import Control.Arrow ( (***) )
import Control.Lens ( (%~) )
import Control.Monad ( foldM )
import Data.Foldable ( foldrM )
import Data.List ( partition, genericLength, sortBy )
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.Reader ( ReaderT, runReaderT, asks )
import Control.Monad.Trans.State.Strict ( gets, modify, StateT(..) )
import qualified Data.HashSet as HS
import qualified Data.IntSet as IS
import Data.Function ( on )
import qualified Data.Map as M

import Prelude hiding ( lex )

import DSL.ComponentsAndWiringParser ( PortOrNamedBoundary(..)
                                     , ComponentsAndWiring(..)
                                     , NetDefinition(..), InOutTest(..)
                                     , WiringDefinition(..), PlaceDef(..) )
import DSL.Expr ( RawExpr(..), SugarExpr(..), InterleavingMarkedNet )
import Marking ( TokenStatus(..), WildCardMarks(..), listToMarkingList )
import Nets ( NetWithBoundaries(..), PortType(..), NetTransition(..)
            , emptyNetTransition, leftBounds, rightBounds, produceAts
            , consumeFroms, queries, isInternalTransition )

-- |'netDefinitionToMarkedNet' checks a given 'NetDefinition' for consistency
-- and correctness. Checks are made for duplicate place/boundary names, and
-- unbound names in transitions
netDefinitionToMarkedNet :: NetDefinition -> Either String InterleavingMarkedNet
netDefinitionToMarkedNet
    (NetDefinition wantInterleaving name places lBounds rBounds trans) = do
    pMap <- makePMap
    bMap <- makeBMap M.empty LeftBoundary lBounds
    bMap' <- makeBMap bMap RightBoundary rBounds
    let (initMark, finalMark) = (listToMarkingList *** listToMarkingList) .
            unzip . map snd . sortBy (compare `on` fst) . M.elems $ pMap
    transList <- mapM (processTrans pMap bMap') trans
    let toHS = HS.fromList *** HS.fromList
        (iTrans, eTrans) = toHS . partition isInternalTransition $ transList
        markedNet = (finalMark, NetWithBoundaries l r 0 initMark iTrans eTrans)
    return (wantInterleaving, markedNet)
  where
    l = genericLength lBounds
    r = genericLength rBounds

    makePMap :: Either String
                    (M.Map String (Int, (TokenStatus, WildCardMarks)))
    makePMap = foldM pMapInserter M.empty $ zip [0..] places

    pMapInserter soFar (index, PlaceDef pName iMark wMark) =
        let val = (index, (iMark, wMark))
        in checkPresenceInsert pName val soFar

    -- Insert names into a map with their index, making sure dups are avoided.
    makeBMap :: M.Map String (Int, PortType) -> PortType -> [String]
             -> Either String (M.Map String (Int, PortType))
    makeBMap initMap side names =
        foldM bMapInserter initMap $ zip (map (, side) [0..]) names

    bMapInserter soFar (pos, bName) = checkPresenceInsert bName pos soFar

    checkPresenceInsert k v m =
        if k `M.member` m
            then fail $ "Duplicate name: " ++ k
            else return $ M.insert k v m

    processTrans :: M.Map String (Int, (TokenStatus, WildCardMarks))
                 -> M.Map String (Int, PortType) -> [PortOrNamedBoundary]
                 -> Either String NetTransition
    processTrans pMap bMap = foldrM inserter emptyNetTransition
      where
        addI lens i nt = return $ (lens %~ IS.insert i) nt

        inserter port nt = case port of
            (Port pName pType) -> case pName `M.lookup` pMap of
                Nothing -> fail $ "Unknown port name: " ++ pName
                                  ++ " in " ++ name
                (Just (i, _)) -> case pType of
                    In -> addI produceAts i nt
                    Out -> addI consumeFroms i nt
                    Test -> addI queries i nt
            (NamedBoundary bName) -> do
                let failMsg = "Unknown boundary: " ++ bName
                case M.lookup bName bMap of
                    Nothing -> fail failMsg
                    Just (i, pType) -> case pType of
                        LeftBoundary -> addI leftBounds i nt
                        RightBoundary -> addI rightBounds i nt
                        e -> fail $ "NamedBoundary: " ++ bName ++
                                    " has non-boundary port-type: " ++ show e

-- | Turn a decomposition into a wiring tree and net map, failing if we have
-- unbound or repeated names, or invalid net definitions. We parameterise the
-- import lookup function on @p@, indicating the type of precomputed values.
lookupNames :: (String -> Maybe p)
            -> ComponentsAndWiring
            -> Either String (SugarExpr p, M.Map String InterleavingMarkedNet)
lookupNames getImport
    (ComponentsAndWiring nets (WiringDefinition imports expr)) = do
        ((), netMap) <- runStateT processNets M.empty
        importMap <- processImports imports
        (, netMap) <$> runReaderT (processRawExpr expr) (netMap, importMap)
  where
    processNets = mapM_ processNet nets
    processNet n@(NetDefinition _ name _ _ _ _) = do
        net <- lift (netDefinitionToMarkedNet n)
        existing <- gets (M.lookup name)
        case existing of
            Just _ -> lift $ fail $ "duplicate named net: " ++ name
            Nothing -> modify (M.insert name net)

    lookupImport name = case getImport name of
        Nothing -> Left $ "No such import known: " ++ show name
        Just precomp -> Right (name, precomp)

    processImports = (M.fromList <$>) . mapM lookupImport

    -- Attempt to turn a RawExpr into an SugarExpr by resolving 'Name's.
    processRawExpr (RVar v) = return $ SEVar v
    processRawExpr (RNum n) = return $ SENum n
    processRawExpr RRead = return SERead
    processRawExpr (RName s) = doLookup s
    processRawExpr (RIntCase e1 e2 e3) =
        processRawExpr e1 >>= (\x -> processBin (SEIntCase x) e2 e3)
    processRawExpr (RNSequence e1 e2) = processBin SENSequence e1 e2
    processRawExpr (RBin op e1 e2) = processBin (SEBin op) e1 e2
    processRawExpr (RApp e1 e2) = processBin SEApp e1 e2
    processRawExpr (RLam ty e1) = SELam ty <$> processRawExpr e1
    processRawExpr (RBind e1 e2) = processBin SEBind e1 e2
    processRawExpr (RSeq e1 e2) = processBin SESeq e1 e2
    processRawExpr (RTen e1 e2) = processBin SETen e1 e2

    processBin f e1 e2 = f <$> processRawExpr e1 <*> processRawExpr e2

    doLookup name = do
        existingNet <- asks (M.lookup name . fst)
        case existingNet of
            Just net -> lift . return $ SEConstant net
            Nothing -> do
                existingImport <- asks (M.lookup name . snd)
                case existingImport of
                    Just precomp -> lift . return $ SEPreComputed precomp
                    Nothing ->
                        lift $ fail $ "unknown import/net in wiring: " ++ name
