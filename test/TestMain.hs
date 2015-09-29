{-# LANGUAGE TupleSections, OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

import Control.Arrow ( first, (***) )
import Control.Applicative ( (<$>) )
import Control.Lens ( (%~), over )
import Control.Monad.Identity ( Identity, runIdentity )
import Control.Monad.Trans.Writer ( runWriterT )
import Control.Parallel.Strategies ( runEval )
import qualified Data.Foldable as DF
import Data.List ( sort, partition )
import qualified Data.Map.Strict as M ( fromList, map, mapKeys, insertWith
                                      , lookup )
import Data.Maybe ( fromJust )
import Data.Monoid ( Any(..), mempty )
import qualified Data.HashSet as HS
import qualified Data.IntSet as IS
import qualified Data.IntMap as IM
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Traversable ( sequenceA )
import Test.Framework ( defaultMainWithOpts, testGroup )
import Test.Framework.Providers.HUnit ( testCase, hUnitTestToTests )
import Test.Framework.Providers.QuickCheck2 ( testProperty )
import Test.Framework.Options ( TestOptions'(..) )
import Test.Framework.Runners.Options ( RunnerOptions'(..) )
import Test.Framework.Runners.Console ( interpretArgsOrExit )
import Test.Framework.Seed ( Seed(..) )
import Test.QuickCheck ( forAll, choose, Property, suchThat, arbitrary, shrink
                       , forAllShrink )
import Test.HUnit ( Assertion, (@?=), Test(TestCase, TestList, TestLabel)
                  , assertBool )
import System.Environment ( getArgs )

import LOLANets ( unparseLOLANet )
import Marking ( TokenStatus(..), listToMarkingList, WildCardMarks(..) )
import Minimisation ( generateSimRel, canDoAllActionsOf, initRel, minimise
                    , prune, deadStates )
import Nets ( NetWithBoundaries(..), tensor, compose, NetTransition(..)
            , emptyNetTransition, net2LLNet, leftBounds, produceAts, consumeFroms
            , queries, rightBounds, syncs, isInternalTransition, net2LOLANet )
import ProcessExpr ( NFALang(..), WithId(..), exprEval )
import NFA ( NFA(..), toNFAWithMarking, subsetConstruction, toNFA
           , NFAWithBoundaries(..), epsilonSubsetConstruction, notInConflict
           , epsMinimise, tensor, epsBisimEquiv, epsilonCloseNFA, modifyNFAWB
           , quotientByPartition, renumberNFA, equivalenceHKC, BoundarySide(..)
           , commonSharedBDD, BoundaryPos(..) )
import PEP ( llNet2Dot )
import qualified NFA ( compose )
import NFAGen ()
import NetGen ()
import ParseNFA
import LTS ( LTS(..) )
import qualified MTBDD
import MTBDD.Internals
import DSL.ComponentsAndWiringParser ( ComponentsAndWiring(..)
                                     , WiringDefinition(..) )
import DSL.ProcessParse ( lookupNames )
import DSL.RawExprParser ( parseRawExpr )
import DSL.Expr ( Type(..), checkType, Value(..), Expr(..), VarId(..) )

import Util ( unlines )
import Prelude hiding ( unlines )

main = do
    args <- getArgs
    goWithArgs args

goWithArgs args = do
    ropts <- interpretArgsOrExit args
    let opts = ropts
               { ropt_test_options = Just $
                  mempty
                  { topt_seed = Just RandomSeed
                  , topt_maximum_generated_tests = Just 1000
                  , topt_maximum_test_size = Just 100
                  }
               }
    defaultMainWithOpts tests opts

tests =
    [ testGroup "conflicting trans"
        [ testCase "prod/consume same place" prodConsumeSamePlace
        , testCase "consume from same place" consumeSamePlace
        , testCase "produce at same place" produceSamePlace
        , testCase "consume different places" consumeDiffPlaces
        , testCase "produce different places" produceDiffPlaces
        , testCase "produce consume different places" produceConsumeDiffPlaces
        , testCase "multiple queries of same place" queriesSamePlace
        , testCase "sync on same internal boundary" syncCommonBoundary
        ]
    , testGroup "to NFA"
        [ testCase "simple net to nfa" simpleToNFA
        , testCase "epsilon loops" epsilonLoopsInNFA
        , testCase "interleaving test" useInterleaving
        , testCase "to NFA1" toNFA1
        , testCase "to NFA2" toNFA2
        , testCase "to NFA3" toNFA3
        ]
    , testGroup "composition of Nets"
        [ testProperty "tensor id nets" prop_tensor_ids_Nets
        , testCase "compose nets" composeNets
        , testCase "compose nets2" composeNets2
        , testCase "compose nets3" composeNets3
        , testCase "compose nets4" composeNets4
        , testCase "compose nets5" composeNets5
        , testCase "compose nets6" composeNets6
        , testCase "compose nets7" composeNets7
        , testCase "compose nets8" composeNets8
        , testCase "compose nets9" composeNets9
        , testCase "compose nets10" composeNets10
        , testCase "compose nets11" composeNets11
        , testCase "compose nets12" composeNets12
        , testCase "compose nets13" composeNets13
        , testCase "compose nets14" composeNets14
        , testCase "compose nets15" composeNets15
        , testCase "compose nets16" composeNets16
        , testCase "compose nets17" composeNets17
        , testCase "compose nets18" composeNets18
        , testCase "compose nets19" composeNets19
        , testCase "compose nets20" composeNets20
        , testCase "tensor nets" tensorNets
        , testCase "tensor nets2" tensorNets2
        ]
    , testGroup "composition of NFAs"
        [ testCase "really simple compose" reallySimpleCompose
        , testCase "dup compose" dupCompose
        , testCase "simpler compose" simplerCompose
        , testCase "simple compose" simpleCompose
        , testCase "simple tensor" simpleTensor
        , testCase "tensor with ID above" tensorWithIDAbove
        , testCase "tensor with ID below" tensorWithIDBelow
        , testCase "tensor 3 IDs" tensor3ID
        , testCase "eps compositionality" composeEps
        , testCase "compose opb" composeOPB
        , testCase "compose hiding trans" composeHiding
        , testCase "composition tensor id" composeTensorId
        , testCase "tensor uneven nets" tensorUnevenNets
        ]
    , testGroup "BDD composition"
        [ testCase "bdd composition 1" bddComposition1
        , testCase "bdd composition 2" bddComposition2
        , testCase "bdd composition 3" bddComposition3
        , testCase "bdd composition 4" bddComposition4
        ]
    , testGroup "NFA subset constructions"
        [ testCase "subset construction" subsetConstr
        , testCase "eps subset construction" epsSubsetConstr
        ]
    , testGroup "NFA partition refinement by bisim"
        [ testCase "bisim part ref a" bisimPartRefA
        , testCase "bisim part ref b" bisimPartRefB
        , testCase "bisim part ref c" bisimPartRefC
        , testCase "bisim part ref d" bisimPartRefD
        , testCase "bisim part ref e" bisimPartRefE
        ]
    , testGroup "functoriality" $
        hUnitTestToTests (TestLabel "examples compose functoriality" $
            TestList exampleComposeFunctoriality)
        ++
        [ testProperty "compose functoriality" prop_compose_functoriality
        , testProperty "compose minimise functoriality" prop_composeminimise_functoriality
        , testProperty "tensor functoriality" prop_tensor_functoriality
        , testProperty "tensor minimise functoriality" prop_tensorminimise_functoriality
        ]
    , testGroup "NFA eps closure"
        [ testCase "eps closure" epsilonClosure
        , testCase "buffer epsmin" bufferEpsMin
        ]
    , testGroup "NFA quotienting"
        [ testCase "nfa quotient" quotientNFA
        , testCase "nfa quotient 2" quotientNFA2
        ]
    , testGroup "NFA equivalence"
        [ testCase "nfa equivalence" equivalenceNFA
        ]
    , testGroup "NFA minimisation" $
        hUnitTestToTests (TestLabel "Can do Actions" $ TestList canDoActions)
        ++
        [ testCase "lookahead sim generation mayr fig6" mayrfig6
        , testCase "lookahead sim generation mayr fig6 B" mayrfig6B
        , testCase "initRel generation" initRelGeneration
        , testCase "simRel generation a" genSimRela
        , testCase "simRel generation b 1step fail" genSimRelb1
        , testCase "simRel generation b 2step fail" genSimRelb2
        , testCase "simRel generation c" genSimRelc
        , testCase "simRel generation d" genSimReld
        , testCase "simRel generation e" genSimRele
        , testCase "prune transitions" pruneTransitions
        , testCase "dead States" getDeadStates
        , testCase "dead states with loops" dontKillNonDeadStates
        , testCase "dead states init is final" deadStatesInitIsFinal
        , testProperty "minimise preserve lang" prop_minimise_preserve_lang
        ]
    , testGroup "Evaluation"
        [ testCase "Recursive function" evalRecFunction
        , testCase "Unused bind" evalUnusedBind
        ]
    , testGroup "Type Checking"
        [ testCase "Type checking1" typeChecking1
        ]
    , testGroup "To strings"
        [ testCase "simple to DotNet" simpleDotNet
        , testCase "simple to LOLANet" simpleLOLANet
        ]
    ]

composeNFA x y = case comp of
    Nothing -> Nothing
    Just c -> if isOkNFAWB c then comp else error $ "not ok compose!" ++ show c
  where
    comp = NFA.compose x y

tensorNFA x y = if isOkNFAWB t then t else error $ "not ok tensor!" ++ show t
  where
    t = NFA.tensor x y

-- Checks if BDDs are OK, i.e. all variables are in < order from root to leaves
isOk :: (Show s, Show l) => LTS s l -> Bool
isOk (LTS trans) = DF.all isOkM trans
  where
    isOkM bdd = DF.all (isOkPath . fst) . MTBDD.getPaths $ bdd

    isOkPath [] = True
    isOkPath [_] = True
    isOkPath ((x,_) : rest@((y,_) : _)) = x < y && isOkPath rest

isOkNFA (NFA lts _ _) = isOk lts
isOkNFAWB (NFAWithBoundaries nfa _ _) = isOkNFA nfa

-- | test that tensoring id nets is correct.
prop_tensor_ids_Nets :: Property
prop_tensor_ids_Nets = forAll (choose (1, 8)) $ \n ->
    ntensor n idNet == expected (fromIntegral n)
  where
    idNet = mkNet 1 1 [] [ [LB 0, RB 0] ]

    ntensor n net = foldr1 Nets.tensor $ replicate n net

    expected n = mkNet n n [] $ map (\i -> [LB i, RB i]) [0.. (n - 1)]

prop_minimise_preserve_lang :: NFA Int Int -> Bool
prop_minimise_preserve_lang nfa = equivalenceHKC (minimise 8 nfa) nfa

lBoundIs n (NetWithBoundaries lbound _ _ _ _ _) = lbound == n
doMin = modifyNFAWB (minimise 8)

toNFALang i nfa = NFALang (WithId nfa i)

prop_tensor_functoriality :: NetWithBoundaries -> NetWithBoundaries -> Bool
prop_tensor_functoriality neta netb =
    toNFALang 0 (toNFA neta `NFA.tensor` toNFA netb) ==
    toNFALang 1 (toNFA (neta `Nets.tensor` netb))

prop_tensorminimise_functoriality :: NetWithBoundaries -> NetWithBoundaries -> Bool
prop_tensorminimise_functoriality neta netb =
    (toNFALang 0 . doMin $ (minNFAa `NFA.tensor` minNFAb)) ==
    (toNFALang 1 . doMin $ toNFA (neta `Nets.tensor` netb))
  where
    minNFAa = doMin (toNFA neta)
    minNFAb = doMin (toNFA netb)

prop_compose_functoriality :: Property
prop_compose_functoriality = forAllShrink arbitrary shrink $
    \neta@(NetWithBoundaries _ rbound _ _ _ _) ->
        forAllShrink (suchThat arbitrary (lBoundIs rbound)) shrink $ \netb ->
            composeFunctoriality neta netb

composeFunctoriality neta netb =
    (toNFALang 0 <$> (toNFA neta `NFA.compose` toNFA netb)) ==
    (toNFALang 1 . toNFA <$> (neta `Nets.compose` netb))

toNTrans (ls, cf, pa, q, rs) =
    map LB ls ++ map CF cf ++ map PA pa ++ map Q q ++ map RB rs

-- Explicitly test instances that have failed before.
exampleComposeFunctoriality = zipWith (curry makeTest) [1..]
    [ (neta1, netb1)
    , (neta2, netb2)
    , (neta3, netb3)
    , (neta4, netb4)
    , (neta5, netb5)
    , (neta6, netb6)
    , (neta7, netb7)
    , (neta8, netb8)
    ]
  where
    makeTest (i, (x, y)) =
        TestLabel ("composeFunctoriality example: " ++ show i) $
            TestCase $ assertBool "" $ composeFunctoriality x y

    neta1 = mkNet 3 4 [Absent,Present] [toNTrans ([2], [1], [], [], [0,1,2,3])]
    netb1 = mkNet 4 4  [Absent,Present,Present] . map toNTrans $
                [([2], [0,1], [0,1], [2], [])
                ,([0,1,3], [], [], [], [])
                ,([], [2], [0,2], [1], [2])]

    neta2 = mkNet 0 3 [] . map toNTrans $ [([], [], [], [], [0,1])]
    netb2 = mkNet 3 2 [Absent] . map toNTrans $
            [([1,2], [], [0], [], [0]),([0,2], [], [], [], [1])]

    neta3 = mkNet 2 1 [Present] [toNTrans ([1,2], [], [], [], [0])]
    netb3 = mkNet 1 3 [Absent,Present,Present]
        [toNTrans ([], [], [], [4], [3])]

    neta4 = mkNet 3 1 [Absent,Absent] [toNTrans ([2], [], [], [], [0])]
    netb4 = mkNet 1 3 [Present,Present] [toNTrans ([], [3], [3], [], [3,4])]

    neta5 = mkNet 1 5 [] [toNTrans ([], [], [], [], [0,2,4])]
    netb5 = mkNet 5 3 [Present] . map toNTrans $
            [([0,4], [], [], [0], [0,2]),([2], [], [], [], [1])]

    neta6 = mkNet 1 1 [Present] [toNTrans ([],[],[],[],[0])]
    netb6 = mkNet 1 2 [] . map toNTrans $
            [([0], [], [], [], [0]),([0], [], [], [], [1])]

    neta7 = mkNet 0 1 [] [toNTrans ([],[],[],[],[0])]

    netb7 = mkNet 1 5 [Present] . map toNTrans $
            [([0], [], [], [], [0,1])
            ,([0], [], [], [], [2,3,4])
            ,([0], [0], [], [], [0])
            ]

    neta8 = mkNet 0 2 [Absent] . map toNTrans $
        [([],[0], [],[],[0]), ([],[],[0],[],[1])]
    netb8 = mkNet 2 1 [Present,Present] . map toNTrans $
        [([],[1],[],[0],[]), ([1],[],[],[],[0]), ([0],[],[1],[0],[])]

prop_composeminimise_functoriality :: Property
prop_composeminimise_functoriality = forAllShrink arbitrary shrink $
    \neta@(NetWithBoundaries _ rbound _ _ _ _) ->
        forAllShrink (suchThat arbitrary (lBoundIs rbound)) shrink $ \netb ->
            let minCompose =
                    doMin (toNFA neta) `NFA.compose` doMin (toNFA netb)
            in (toNFALang 0 . doMin <$> minCompose) ==
               (toNFALang 1 . doMin . toNFA <$> (neta `Nets.compose` netb))

toNFAWith :: [WildCardMarks] -> NetWithBoundaries -> NFAWithBoundaries Int
toNFAWith ms = toNFAWithMarking False (listToMarkingList ms)

subsetConstrNFA :: NFA Int Int
subsetConstrNFA = textToNFA [ "0,1"
                            , "0--00->2"
                            , "0--01->3"
                            , "1--11->3"
                            , "2--10->3"
                            , "3"
                            ]

subsetConstr :: Assertion
subsetConstr = renumberNFA (subsetConstruction subsetConstrNFA) @?= expected
  where
    expected = textToNFA [ "1"
                         , "0--*->0"
                         , "1--00->2"
                         , "1--01,11->3"
                         , "1--10->0"
                         , "2--00,01,11->0"
                         , "2--10->3"
                         , "3--*->0"
                         , "3"
                         ]

epsSubsetConstr :: Assertion
epsSubsetConstr =
    renumberNFA (epsilonSubsetConstruction subsetConstrNFA) @?= expected
  where
    expected = textToNFA [ "1"
                         , "0--*->0"
                         , "1--00->2"
                         , "1--01,10,11->3"
                         , "2--00,01,11->0"
                         , "2--10->3"
                         , "3--*->0"
                         , "3"
                         ]

data TranPort = LB Int
              | CF Int
              | PA Int
              | Q Int
              | RB Int
              | S Int

mkNet l r m ts = NetWithBoundaries l r 0 (listToMarkingList m) its ets
  where
    toHS = HS.fromList *** HS.fromList
    (its, ets) = toHS . partition isInternalTransition . listsToTrans $ ts

listsToTrans :: [[TranPort]] -> [NetTransition]
listsToTrans = map toNT
  where
    toNT = foldr inserter emptyNetTransition
    inserter t = let (lens, i) = case t of
                                LB i -> (leftBounds, i)
                                CF i -> (consumeFroms, i)
                                PA i -> (produceAts, i)
                                Q i ->  (queries, i)
                                RB i -> (rightBounds, i)
                                S i -> (syncs, i)
                 in lens %~ IS.insert i

bufferEpsMin :: Assertion
bufferEpsMin = epsMinimise getBufferNFA @?= expected
  where
    expected = textToNFAWB [ "0"
                           , "0--/1->1"
                           , "0--/0->0"
                           , "1--/0->1"
                           , "1--/1->2"
                           , "2--/*->2"
                           , "2"
                           ]

    getBufferNFA = toNFAWith [No, Yes, No, Yes] net

    net = fromJust $
        lend `Nets.compose` fromJust (bnet `Nets.compose` bnet)

    lend = mkNet 0 1 [] [ [RB 0] ]

    bnet = mkNet 1 1 [Present, Absent]
        [ [LB 0, PA 0, CF 1]
        , [RB 0, CF 0, PA 1]
        ]

-- A simple net with a single place connected to two right boundaries.
dupNet :: NFAWithBoundaries Int
dupNet = toNFAWith [No] $
    mkNet 0 2 [Present]
        [ [CF 0, RB 0]
        , [CF 0, RB 1]
        ]

simpleToNFA :: Assertion
simpleToNFA = dupNet @?= expected
  where
    expected = textToNFAWB [ "0"
                           , "0--/00->0"
                           , "0--/10->1"
                           , "0--/01->1"
                           , "1--/00->1"
                           , "1"
                           ]

epsilonLoopsInNFA :: Assertion
epsilonLoopsInNFA = actual @?= expected
  where
    actual = epsMinimise . toNFAWith [No, No, No] $ net

    -- A net with 3 places, with 0->1, 1->2, and 2->3, with connections to the
    -- boundary to observe internal trans firing.
    net = mkNet 0 3 [Present, Absent, Absent]
        [ [CF 0, PA 1, RB 0]
        , [CF 1, PA 2, RB 1]
        , [CF 2, RB 2]
        ]

    addErr = MTBDD.unary $ \s -> if S.null s then S.singleton 4 else s

    -- The node numbering of epsMinimise takes 0 as the error state.
    changeID = (`mod` 5) . (+ 1)
    changeIDs = S.map changeID

    (NFAWithBoundaries (NFA (LTS trans) isInit isFinal) l r) =
               textToNFAWB [ "1"
                           , "0--/000->0"
                           , "0--/100->1"
                           , "1--/000->1"
                           , "1--/010->2"
                           , "2--/000->2"
                           , "2--/001->3"
                           , "3--/000->3"
                           , "4--/***->4"
                           , "4"
                           ]

    expected = NFAWithBoundaries (NFA (LTS trans') isInit isFinal) l r

    trans' = M.mapKeys changeID . M.map (MTBDD.unary changeIDs) .
        M.map addErr $ trans

forgetInternal (NetWithBoundaries l r _ m its ets) =
    NetWithBoundaries l r 0 m (HS.map removeInternal its)
        (HS.map removeInternal ets)
  where
    removeInternal = over syncs (const IS.empty)

composeNets :: Assertion
composeNets = (forgetInternal <$> Nets.compose neta netb) @?= Just expected
  where
    neta = mkNet 1 3 [Absent,Absent,Absent]
        [ [CF 0, RB 0, RB 1]
        , [LB 0]
        , [CF 0, RB 0]
        , [CF 1, RB 1]
        , [CF 2, RB 2]
        ]

    netb = mkNet 3 1 [Present, Present]
        [ [PA 0, LB 0, LB 1]
        , [RB 0]
        , [PA 1, LB 0, LB 2]
        ]

    expected = mkNet 1 1 [Absent, Absent, Absent, Present, Present]
        [ [CF 0, CF 1, PA 3]
        , [LB 0]
        , [RB 0]
        , [CF 0, PA 3]
        , [CF 0, CF 2, PA 4]
        ]

composeNets2 :: Assertion
composeNets2 = (forgetInternal <$> Nets.compose neta netb) @?= Just expected
  where
    neta = mkNet 0 3 [Absent,Absent,Absent]
        [ [CF 0, RB 0]
        , [CF 2, RB 2]
        ]

    netb = mkNet 3 0 [Present, Present]
        [ [PA 0, LB 0, LB 1]
        , [PA 1, LB 0, LB 2]
        ]

    expected = mkNet 0 0 [Absent, Absent, Absent, Present, Present]
        [ [CF 0, CF 2, PA 4] ]

composeNets3 :: Assertion
composeNets3 = (forgetInternal <$> Nets.compose neta netb) @?= Just expected
  where
    neta = mkNet 2 2 [] [ [LB 0, RB 0], [LB 1, RB 1] ]

    netb = mkNet 2 0 [] [ [LB 0, LB 1], [LB 1] ]

    expected = mkNet 2 0 [] [ [LB 0, LB 1], [LB 1] ]

composeNets4 :: Assertion
composeNets4 = (forgetInternal <$> Nets.compose neta netb) @?= Just expected
  where
    neta = mkNet 3 4 [] [ [LB 2, RB 3], [RB 0, RB 2, LB 0], [LB 1, RB 1] ]

    netb = mkNet 4 3 [] [ [ LB 0, RB 0], [ LB 1, RB 2, LB 3], [ LB 2, RB 1] ]

    expected = mkNet 3 3 [] [ [LB 0 , RB 0 , RB 1], [LB 1, LB 2, RB 2] ]

composeNets5 :: Assertion
composeNets5 = (forgetInternal <$> Nets.compose neta netb) @?= Just expected
  where
    neta = mkNet 0 5 [Absent,Absent,Absent]
        [ [CF 0, RB 0], [RB 2], [CF 1, RB 2], [CF 2, RB 3, RB 4] ]

    netb = mkNet 5 0 [Present, Present, Present]
        [ [PA 0, LB 0, LB 2], [PA 1, LB 1], [PA 2, LB 0, LB 3, LB 4] ]

    expected = mkNet 0 0 [Present, Present, Present, Absent, Absent, Absent]
        [ [CF 3, PA 0], [CF 3, CF 4, PA 0], [CF 3, CF 5, PA 2] ]

composeNets6 :: Assertion
composeNets6 = (forgetInternal <$> Nets.compose neta netb) @?= Just expected
  where
    expected = mkNet 0 0 [Present, Present, Absent] []

    neta = mkNet 0 3 [Absent] [ [CF 0, RB 0, RB 1, RB 2] ]

    netb = mkNet 3 0 [Present, Present]
        [ [PA 0, LB 0, LB 1], [PA 1, LB 0, LB 2] ]

composeNets7 :: Assertion
composeNets7 = (forgetInternal <$> Nets.compose neta netb) @?= Just expected
  where
    expected = mkNet 0 0 [Absent, Absent, Absent, Present, Present]
        [ [Q 3, Q 4, PA 1] ]

    neta = mkNet 0 4 [Present, Present]
        [ [CF 0, RB 0], [Q 0, RB 1], [CF 1, RB 2], [Q 1, RB 3] ]

    netb = mkNet 4 0 [Absent, Absent, Absent]
        [ [LB 0, LB 1, PA 0], [LB 1, LB 3, PA 1], [LB 2, LB 3, PA 2] ]

composeNets8 :: Assertion
composeNets8 = (forgetInternal <$> Nets.compose neta netb) @?= Just expected
  where
    expected = mkNet 0 0 [Absent, Absent, Absent, Absent]
        [ [CF 1, PA 3], [CF 0, CF 2, PA 3] ]

    neta = mkNet 0 2 [Absent, Absent, Absent]
        [ [CF 0, RB 0], [CF 1, RB 0, RB 1], [CF 2, RB 1] ]

    netb = mkNet 2 0 [Absent] [ [LB 0, LB 1, PA 0] ]

composeNets9 :: Assertion
composeNets9 = (forgetInternal <$> Nets.compose neta netb) @?= Just expected
  where
    expected = mkNet 0 1 [] [ [RB 0] ]

    neta = mkNet 0 2 [] [ [RB 0, RB 1] ]

    netb = mkNet 2 1 [] [ [LB 0, RB 0], [LB 1] ]

composeNets10 :: Assertion
composeNets10 = (forgetInternal <$> Nets.compose neta netb) @?= Just expected
  where
    expected = mkNet 0 1 [] []

    neta = mkNet 0 3 [] [ [RB 0, RB 1, RB 2] ]

    netb = mkNet 3 1 [] [ [LB 0, LB 2, RB 0], [LB 1, LB 2] ]

composeNets11 :: Assertion
composeNets11 = (forgetInternal <$> Nets.compose neta netb) @?= Just expected
  where
    expected = mkNet 1 2 [Present] [ [RB 0], [RB 1] ]

    neta = mkNet 1 1 [Present] [ [RB 0] ]

    netb = mkNet 1 2 [] [ [LB 0, RB 0], [LB 0, RB 1] ]

composeNets12 :: Assertion
composeNets12 = (forgetInternal <$> Nets.compose neta netb) @?= Just expected
  where
    expected = mkNet 0 5 [Present]
        [ [RB 0, RB 1], [RB 2, RB 3, RB 4], [CF 0, RB 0] ]

    neta = mkNet 0 1 [] [ [RB 0] ]

    netb = mkNet 1 5 [Present]
        [ [LB 0, RB 0, RB 1], [LB 0, RB 2, RB 3, RB 4], [LB 0, CF 0, RB 0] ]

composeNets13 :: Assertion
composeNets13 = (forgetInternal <$> Nets.compose neta netb) @?= Just expected
  where
    expected = mkNet 2 2 [Absent]
        [ [PA 0, RB 1], [CF 0, LB 1] ]

    neta = mkNet 2 2 [Absent] [ [CF 0, RB 0], [PA 0, RB 1], [LB 1, CF 0] ]

    netb = mkNet 2 2 [] [ [LB 0, LB 1],  [RB 1, LB 1] ]

composeNets14 :: Assertion
composeNets14 = (forgetInternal <$> comp) @?= Just expected
  where
    expected = mkNet 1 1 [Absent, Absent, Absent, Absent]
        [ [CF 0, CF 1, CF 2, CF 3, LB 0, RB 0] ]

    comp = compa >>= \n -> Nets.compose n n

    compa = Nets.compose neta (Nets.tensor netb neti)

    neta = mkNet 1 2 [Absent] [ [CF 0, LB 0, RB 0, RB 1] ]
    netb = mkNet 1 0 [Absent] [ [CF 0, LB 0] ]
    neti = mkNet 1 1 [] [ [LB 0, RB 0] ]

composeNets15 :: Assertion
composeNets15 = (forgetInternal <$> Nets.compose neta netb) @?= Just expected
  where
    expected = mkNet 1 1 [Present, Absent, Absent, Present]
        [ [CF 1, PA 0], [CF 0, PA 1], [CF 2, PA 3], [CF 3, PA 2], [CF 0, PA 2]
        , [RB 0, PA 0], [CF 2, LB 0] ]

    neta = mkNet 1 1 [Absent, Present] trans
    netb = mkNet 1 1 [Present, Absent] trans

    trans = [ [CF 0, PA 1], [CF 1, PA 0], [CF 0, LB 0], [PA 0, RB 0] ]

composeNets16 :: Assertion
composeNets16 = (forgetInternal <$> comp) @?= Just expected
  where
    -- Same as 15, but looped around
    expected = mkNet 0 0 [Present, Absent, Absent, Present]
        [ [CF 1, PA 0], [CF 0, PA 1], [CF 2, PA 3], [CF 3, PA 2], [CF 0, PA 2]
        , [CF 2, PA 0] ]

    comp = do
        c <- Nets.compose neta netb
        let ci = Nets.tensor neti c
        lci <- Nets.compose netl ci
        Nets.compose lci netr

    neta = mkNet 1 1 [Absent, Present] trans
    netb = mkNet 1 1 [Present, Absent] trans
    neti = mkNet 1 1 [] [ [LB 0, RB 0] ]
    netl = mkNet 0 2 [] [ [RB 0, RB 1] ]
    netr = mkNet 2 0 [] [ [LB 0, LB 1] ]

    trans = [ [CF 0, PA 1], [CF 1, PA 0], [CF 0, LB 0], [PA 0, RB 0] ]

composeNets17 :: Assertion
composeNets17 = comp @?= Just expected
  where
    etrans = HS.fromList $ listsToTrans
        [ [ LB 0, RB 0, S 0, S 2 ]
        , [ LB 1, RB 1, S 1, S 3 ]
        ]
    expected = NetWithBoundaries 2 2 4 (listToMarkingList []) HS.empty etrans

    comp = Nets.compose idNet idNet >>= (`Nets.compose` idNet)

    idNet = mkNet 2 2 [] [ [LB 0, RB 0], [LB 1, RB 1] ]

composeNets18 :: Assertion
composeNets18 = Nets.compose neta netb @?= Just expected
  where
    etrans = HS.fromList $ listsToTrans
        [ [ LB 0, PA 0, S 2, S 3 ]
        , [ LB 1, CF 1, S 1]
        ]
    expected = NetWithBoundaries 2 0 4 (listToMarkingList [Absent, Absent])
        HS.empty etrans

    neta = NetWithBoundaries 2 2 2 (listToMarkingList [Absent, Absent])
        HS.empty aetrans
    aetrans = HS.fromList $ listsToTrans
        [ [LB 0, RB 0], [RB 1, PA 0], [CF 1, LB 1, S 1] ]

    netb = mkNet 2 0 [] [ [LB 0, LB 1] ]

composeNets19 :: Assertion
composeNets19 = Nets.compose neta neta @?= Just expected
  where
    -- All transitions connect to left/right boundary and synced on internal
    etrans = HS.fromList . listsToTrans . map ([LB 0, RB 0, S 0] ++) $
        [ [ CF 0, CF 2, PA 1, PA 3 ] -- Both start
        , [ CF 1, CF 3, PA 0 ] -- Both stop, only left restartable
        , [ CF 1, CF 2, PA 3 ] -- Left stop unrestart, right start
        , [ CF 1, CF 3, PA 2 ] -- Both stop, only right restartable
        , [ CF 0, CF 3, PA 1, PA 2] -- right stop restart, left start
        , [ CF 1, CF 2, PA 0, PA 3] -- left stop restart, right start
        , [ CF 0, CF 3, PA 1] -- left start, right stop unrestart
        , [ CF 1, CF 3] -- both stop unrestart
        , [ CF 1, CF 3, PA 0, PA 2] -- both stop restart
        ]
    expected = NetWithBoundaries 1 1 1
        (listToMarkingList [Present, Absent, Present, Absent])
        HS.empty etrans

    -- All trans connect to the boundaries.
    -- Models a two state system that can start, stop and possibly restart
    neta = mkNet 1 1 [Present, Absent] . map ([LB 0, RB 0] ++) $
            [ [CF 0, PA 1] -- Start
            , [CF 1, PA 0] -- Stop, able to restart
            , [CF 1, LB 0] -- Stop, unable to restart
            ]

composeNets20 :: Assertion
composeNets20 = loopAround (Nets.compose neta neta) @?= Just expected
  where
    -- All transitions connect to left/right boundary and synced on internal
    itrans = HS.fromList . listsToTrans . map ([S 0, S 1, S 2, S 3] ++) $
        [ [ CF 0, CF 2, PA 1, PA 3 ] -- Both start
        , [ CF 1, CF 3, PA 0 ] -- Both stop, only left restartable
        , [ CF 1, CF 2, PA 3 ] -- Left stop unrestart, right start
        , [ CF 1, CF 3, PA 2 ] -- Both stop, only right restartable
        , [ CF 0, CF 3, PA 1, PA 2] -- right stop restart, left start
        , [ CF 1, CF 2, PA 0, PA 3] -- left stop restart, right start
        , [ CF 0, CF 3, PA 1] -- left start, right stop unrestart
        , [ CF 1, CF 3] -- both stop unrestart
        , [ CF 1, CF 3, PA 0, PA 2] -- both stop restart
        ]
    expected = NetWithBoundaries 0 0 5
        (listToMarkingList [Present, Absent, Present, Absent])
        itrans HS.empty

    -- All trans connect to the boundaries.
    -- Models a two state system that can start, stop and possibly restart
    neta = mkNet 1 1 [Present, Absent] . map ([LB 0, RB 0] ++) $
            [ [CF 0, PA 1] -- Start
            , [CF 1, PA 0] -- Stop, able to restart
            , [CF 1, LB 0] -- Stop, unable to restart
            ]

    loopAround n = n >>= (Nets.compose eta . Nets.tensor id) >>= (`Nets.compose` eps)

    eta = mkNet 0 2 [] [[RB 0, RB 1]]
    eps = mkNet 2 0 [] [[LB 0, LB 1]]
    id = mkNet 1 1 []  [[LB 0, RB 0]]

tensorNets :: Assertion
tensorNets = Nets.tensor neta netb @?= expected
  where
    neta = mkNet 0 3 [Absent,Absent,Absent]
        [ [CF 0 , RB 0 , RB 1]
        , [CF 0 , RB 0]
        , [CF 1 , RB 1]
        , [CF 2 , RB 2]
        ]

    netb = mkNet 3 1 [Present, Present]
        [ [PA 0, LB 0, LB 1]
        , [PA 1, LB 0, LB 2, RB 0]
        ]

    expected = mkNet 3 4 [Absent, Absent, Absent, Present, Present]
        [ [CF 0, RB 0, RB 1]
        , [CF 0, RB 0]
        , [CF 1, RB 1]
        , [CF 2, RB 2]
        , [PA 3, LB 0, LB 1]
        , [PA 4, LB 0, LB 2, RB 3]
        ]

tensorNets2 :: Assertion
tensorNets2 = Nets.tensor neta netb @?= expected
  where
    neta = mkNet 1 3 [Absent,Absent,Absent]
        [ [CF 0, RB 0, LB 0], [CF 2, RB 2] ]

    netb = mkNet 3 0 [Present, Present]
        [ [PA 0, LB 0, LB 1], [PA 1, LB 0, LB 2] ]

    expected = mkNet 4 3 [Absent, Absent, Absent, Present, Present]
        [ [ CF 0, RB 0, LB 0 ]
        , [ CF 2, RB 2 ]
        , [ PA 3, LB 1, LB 2 ]
        , [ PA 4, LB 1, LB 3 ]
        ]

reallySimpleCompose :: Assertion
reallySimpleCompose = composeNFA lopb ropb @?= expected
  where
    expected = Just $ textToNFAWB [ "0"
                                  , "0--/->0,1"
                                  , "1--/->1"
                                  , "1"
                                  ]

    lopb = toNFAWith [No] $
        mkNet 0 1 [Present] [ [CF 0, RB 0] ]

    ropb = toNFAWith [Yes] $
        mkNet 1 0 [Absent] [ [LB 0, PA 0] ]

composeEps :: Assertion
composeEps = res1 @?= res2
  where
    res1 = eClose (fromJust $ composeNFA nfa1 nfa2)
    res2 = eClose (fromJust $ composeNFA (eClose nfa1) (eClose nfa2))

    eClose = modifyNFAWB epsilonCloseNFA

    nfa1 = toNFAWith [No, No, No, Yes] $
        mkNet 1 1 [Present, Absent, Absent, Absent]
             [ [CF 0, PA 1]
             , [CF 1, PA 2, RB 0]
             , [ CF 2, LB 0, PA 3
               , RB 0
               ]
             ]

    nfa2 = toNFAWith [No, No, No, No] $
        mkNet 1 1 [Present, Absent, Absent, Present]
             [ [CF 0, PA 1]
             , [ LB 0, CF 1, PA 2
               , CF 3
               ]
             , [CF 2, RB 0, LB 0]
             ]

composeOPB :: Assertion
composeOPB = res @?= expected
  where
    res = do
        lopb <- composeNFA l opb
        final <- composeNFA lopb r
        return $ modifyNFAWB (minimise 8) $ modifyNFAWB epsilonCloseNFA final

    expected = Just $ textToNFAWB [ "1"
                                  , "1--/->1"
                                  , "1"
                                  ]

    l = toNFAWith [] $ mkNet 0 1 [] [ [RB 0] ]

    opb = toNFAWith [No, Yes] $
        mkNet 1 1 [Present, Absent]
            [ [LB 0, PA 0]
            , [ CF 0, PA 1, RB 0 ]
            , [CF 1, PA 0]
            ]

    r = toNFAWith [] $ mkNet 1 0 [] [ [LB 0] ]

composeHiding :: Assertion
composeHiding = composeNFA l r @?= expected
  where
    expected = Just $ textToNFAWB [ "0"
                                  , "0--00/->0"
                                  , "0--10/->1"
                                  , "0--01/->1"
                                  , "1--00/->1"
                                  , "0,1"
                                  ]

    l = textToNFAWB [ "0"
                    , "0--00/00->0"
                    , "0--11/11->0"
                    , "0--10/10->1"
                    , "0--01/01->1"
                    , "0--11/11->1"
                    , "1--00/00->1"
                    , "1--01/11->1"
                    , "0,1"
                    ]

    r = textToNFAWB [ "0"
                    , "0--00/,01/,10/->0"
                    , "0"
                    ]

composeTensorId :: Assertion
composeTensorId = res @?= expected
  where
    res = tensorNFA l (tensorNFA id id)

    expected =
        textToNFAWB [ "0"
                    , "0--00/000,01/001,10/010,11/011->0"
                    , "0--00/100,01/101,10/110,11/111->1"
                    , "1--00/000,01/001,10/010,11/011->1"
                    , "0,1"
                    ]

    l = textToNFAWB [ "0"
                    , "0--/1->1"
                    , "0--/0->0"
                    , "1--/0->1"
                    , "0,1"
                    ]

    id = textToNFAWB [ "0"
                     , "0--1/1->0"
                     , "0--0/0->0"
                     , "0"
                     ]

tensorUnevenNets :: Assertion
tensorUnevenNets = res @?= expected
  where
    res = tensorNFA l r

    expected =
        textToNFAWB [ "0"
                    , "0--1/1->0"
                    , "0"
                    ]

    l = textToNFAWB [ "0"
                    , "0--1/->0"
                    , "0"
                    ]

    r = textToNFAWB [ "0"
                    , "0--/1->0"
                    , "0"
                    ]

relabelBDD (MTBDD top (core, leaves)) = MTBDD top' (core', leaves)
  where
    top' = renameMap IM.! top

    (_, core', renameMap) =
        IM.foldlWithKey renamer (0, IM.empty, IM.empty) core

    renamer (next, newCore, renameMap) i node = (next', newCore', renameMap')
      where
        next' = next + 1
        newCore' = IM.insert next node' newCore
        renameMap' = IM.insert i next renameMap
        node' = case node of
            Leaf _ -> node
            Branch v l r -> Branch v (renameMap IM.! l) (renameMap IM.! r)

bddFromPaths :: (Ord v, Ord e, Eq e) => [([(v, Bool)], S.Set e)]
             -> MTBDD.MTBDD v (S.Set e)
bddFromPaths = foldr1 (MTBDD.||) . map (uncurry (MTBDD.unitWithVars S.empty))

toBDDPaths mbSide size init =
    zip (map (zip vars) assigns) $ map S.singleton [init..]
  where
    assigns = sequenceA $ replicate (2 ^ size) [False, True]
    vars = case mbSide of
        Nothing -> sort . map BoundaryPos $
            map (,L) [0..(size - 1)] ++ map (,R) [0..(size - 1)]
        Just side -> map (BoundaryPos . (,side)) [0..(size * 2) - 1]

bddComposition1 :: Assertion
bddComposition1 = relabelBDD (commonSharedBDD x y) @?= expected
  where
    expected = bddFromPaths . map (first (map (first BoundaryPos))) $
        [ ( [((0,L),False),((1,L),False),((0,R),False),((1,R),False)]
          , S.fromList [(0,16),(1,20),(2,24),(3,28)])
        , ( [((0,L),False),((1,L),False),((0,R),False),((1,R),True)]
          , S.fromList [(0,17),(1,21),(2,25),(3,29)])
        , ( [((0,L),False),((1,L),False),((0,R),True),((1,R),False)]
          , S.fromList [(0,18),(1,22),(2,26),(3,30)])
        , ( [((0,L),False),((1,L),False),((0,R),True),((1,R),True)]
          , S.fromList [(0,19),(1,23),(2,27),(3,31)])
        , ( [((0,L),False),((1,L),True),((0,R),False),((1,R),False)]
          , S.fromList [(4,16),(5,20),(6,24),(7,28)])
        , ( [((0,L),False),((1,L),True),((0,R),False),((1,R),True)]
          , S.fromList [(4,17),(5,21),(6,25),(7,29)])
        , ( [((0,L),False),((1,L),True),((0,R),True),((1,R),False)]
          , S.fromList [(4,18),(5,22),(6,26),(7,30)])
        , ( [((0,L),False),((1,L),True),((0,R),True),((1,R),True)]
          , S.fromList [(4,19),(5,23),(6,27),(7,31)])
        , ( [((0,L),True),((1,L),False),((0,R),False),((1,R),False)]
          , S.fromList [(8,16),(9,20),(10,24),(11,28)])
        , ( [((0,L),True),((1,L),False),((0,R),False),((1,R),True)]
          , S.fromList [(8,17),(9,21),(10,25),(11,29)])
        , ( [((0,L),True),((1,L),False),((0,R),True),((1,R),False)]
          , S.fromList [(8,18),(9,22),(10,26),(11,30)])
        , ( [((0,L),True),((1,L),False),((0,R),True),((1,R),True)]
          , S.fromList [(8,19),(9,23),(10,27),(11,31)])
        , ( [((0,L),True),((1,L),True),((0,R),False),((1,R),False)]
          , S.fromList [(12,16),(13,20),(14,24),(15,28)])
        , ( [((0,L),True),((1,L),True),((0,R),False),((1,R),True)]
          , S.fromList [(12,17),(13,21),(14,25),(15,29)])
        , ( [((0,L),True),((1,L),True),((0,R),True),((1,R),False)]
          , S.fromList [(12,18),(13,22),(14,26),(15,30)])
        , ( [((0,L),True),((1,L),True),((0,R),True),((1,R),True)]
          , S.fromList [(12,19),(13,23),(14,27),(15,31)])
        ]
    x = bddFromPaths $ toBDDPaths Nothing 2 0
    y = bddFromPaths $ toBDDPaths Nothing 2 16

bddComposition2 :: Assertion
bddComposition2 = relabelBDD (commonSharedBDD x y) @?= expected
  where
    expected = bddFromPaths [([], S.fromList [(0,4),(1,5),(2,6),(3,7)])]

    x = bddFromPaths $ toBDDPaths (Just R) 1 0
    y = bddFromPaths $ toBDDPaths (Just L) 1 4

bddComposition3 :: Assertion
bddComposition3 = relabelBDD (commonSharedBDD x y) @?= expected
  where
    withVars =
        map (first (zip (map BoundaryPos [(0, L), (1, L), (0, R), (1, R)])))

    x = bddFromPaths . withVars $
            [ ([False, True, False, True], S.singleton 2)
            , ([True, False, False, False], S.singleton 1)
            , ([False, False, False, False] , S.singleton 0)
            ]

    y = bddFromPaths . withVars $
            [ ([False, True, False, False], S.singleton 2)
            , ([True, False, True, False] , S.singleton 1)
            , ([False, False, False, False] , S.singleton 0)
            ]

    expected = bddFromPaths . withVars $
        [ ([False, True, False, False], S.singleton (2,2))
        , ([True, False, False, False], S.singleton (1,0))
        , ([False, False, False, False], S.singleton (0,0))
        ]

bddComposition4 :: Assertion
bddComposition4 = relabelBDD (commonSharedBDD x y) @?= expected
  where
    x = bddFromPaths . map (first (map (first BoundaryPos))) $
            [ ([((0, R), True)] , S.singleton 3)
            , ([((0, R), False), ((1, R), True)] , S.singleton 2)
            , ([((0, R), False), ((1, R), False)] , S.fromList [0, 1])
            ]

    y = bddFromPaths . map (first (map (first BoundaryPos))) $
            [ ([((0, L), True)] , S.singleton 3)
            , ([((0, L), False), ((1, L), True)] , S.singleton 2)
            , ([((0, L), False), ((1, L), False)] , S.fromList [0, 1])
            ]

    expected = bddFromPaths
        [([], S.fromList [(0,0), (0, 1), (1, 0), (1, 1), (2, 2), (3, 3)])]

dupCompose :: Assertion
dupCompose = composeNFA l r @?= expected
  where
    expected = Just $ textToNFAWB [ "0"
                                  , "0--/->0,1"
                                  , "1--/->1"
                                  , "1"
                                  ]

    l = toNFAWith [No] $
        mkNet 0 2 [Present]
            [ [CF 0, RB 0]
            , [CF 0, RB 1]
            ]

    r = toNFAWith [Yes] $
        mkNet 2 0 [Absent]
            [ [LB 0, PA 0]
            , [LB 1, PA 0]
            ]

simplerCompose :: Assertion
simplerCompose = composeNFA prod cons @?= expected
  where
    expected = Just $ textToNFAWB [ "0"
                                  , "0--/0->0,1,3"
                                  , "1--/0->1"
                                  , "1--/1->2"
                                  , "3--/0->3"
                                  , "3--/1->4"
                                  , "2--/0->2,5"
                                  , "4--/0->4,5"
                                  , "5--/0->5"
                                  , "5--/1->6"
                                  , "6--/0->6"
                                  , "6"
                                  ]

    -- A net with a two places connected to two right boundaries.
    prod = toNFAWith [No, No] $
        mkNet 0 2 [Present, Present]
            [ [CF 0, RB 0]
            , [CF 1, RB 1]
            ]

    -- A net with two input boundaries, which both fill a single place, which
    -- is connected to the right boundary.
    cons = toNFAWith [No] $
        mkNet 2 1 [Absent]
            [ [LB 0, PA 0]
            , [LB 1, PA 0]
            , [CF 0, RB 0]
            ]

simpleCompose :: Assertion
simpleCompose = composeNFA dupNet nfa2 @?= expected
  where
    expected = Just $ textToNFAWB [ "0"
                                  , "0--/0->0,2,4"
                                  , "0--/1->1,3,5"
                                  , "2--/0->2"
                                  , "2--/1->3"
                                  , "1--/0->1,3,5"
                                  , "4--/0->4"
                                  , "4--/1->5"
                                  , "3--/0->3,6"
                                  , "5--/0->5,6"
                                  , "6--/0->6"
                                  , "6--/1->7"
                                  , "7--/0->7"
                                  , "7"
                                  ]

    -- A net with two input boundaries, which fill two different places. These
    -- places share a common target place, which is consumed from to produce at
    -- the right boundary
    nfa2 = toNFAWith [No, No, No] $ mkNet 2 1 [Absent, Absent, Present]
        [ [LB 0, PA 0]
        , [LB 1, PA 1]
        , [CF 0, PA 2]
        , [CF 1, PA 2]
        , [CF 2, RB 0]
        ]

simpleTensor :: Assertion
simpleTensor = tensorNFA nfa nfa @?= expected
  where
    nfa = toNFAWith [No] $
        mkNet 0 1 [Present] [ [CF 0, RB 0] ]

    expected = textToNFAWB [ "0"
                           , "0--/00->0"
                           , "0--/01->1"
                           , "0--/10->2"
                           , "0--/11->3"
                           , "1--/00->1"
                           , "1--/10->3"
                           , "2--/00->2"
                           , "2--/01->3"
                           , "3--/00->3"
                           , "3"
                           ]

tensorWithIDBelow :: Assertion
tensorWithIDBelow = tensorNFA nfa id @?= expected
  where
    id = textToNFAWB [ "0"
                     , "0--0/0,1/1->0"
                     , "0"
                     ]

    -- Problem case where we might re-order the variables if we are not careful
    -- and blindly apply an offset, since the left boundary size is bigger than
    -- the right.
    nfa = textToNFAWB [ "0"
                      , "0--0/,1/->0"
                      , "0--1/->1"
                      , "0"
                      ]

    expected = textToNFAWB [ "0"
                           , "0--00/0,01/1,10/0,11/1->0"
                           , "0--10/0,11/1->1"
                           , "0"
                           ]
tensor3ID :: Assertion
tensor3ID = tensorNFA id (tensorNFA id id) @?= expected
  where
    id = textToNFAWB [ "0"
                     , "0--0/0,1/1->0"
                     , "0"
                     ]


    expected = textToNFAWB [ "0"
                           , "0--000/000,001/001,010/010,011/011,100/100,101/101,110/110,111/111->0"
                           , "0"
                           ]

tensorWithIDAbove :: Assertion
tensorWithIDAbove = tensorNFA id nfa @?= expected
  where
    id = textToNFAWB [ "0"
                     , "0--0/0,1/1->0"
                     , "0"
                     ]

    nfa = textToNFAWB [ "0"
                      , "0--0/0,1/1->0"
                      , "0--1/1->1"
                      , "0"
                      ]

    expected = textToNFAWB [ "0"
                           , "0--00/00,01/01,10/10,11/11->0"
                           , "0--01/01,11/11->1"
                           , "0"
                           ]

testNotConflicting :: [[TranPort]] -> [[[TranPort]]] -> Assertion
testNotConflicting input expected = notInConflict inputSet @?= expectedSet
  where
    inputSet = S.fromList $ listsToTrans input
    expectedSet = S.fromList . map (S.fromList . listsToTrans) $ expected

prodConsumeSamePlace :: Assertion
prodConsumeSamePlace = testNotConflicting input expected
  where
    input = [ [PA 0, LB 0]
            , [CF 0, RB 0]
            ]
    expected = [ []
               , [[PA 0, LB 0]]
               , [[CF 0, RB 0]]
               ]

consumeSamePlace :: Assertion
consumeSamePlace = testNotConflicting input expected
  where
    input = [ [CF 0, LB 0]
            , [CF 0, RB 0]
            ]
    expected = [ []
               , [[CF 0, LB 0]]
               , [[CF 0, RB 0]]
               ]

produceSamePlace :: Assertion
produceSamePlace = testNotConflicting input expected
  where
    input = [ [PA 0, LB 0]
            , [PA 0, RB 0]
            ]
    expected = [ []
               , [[PA 0, LB 0]]
               , [[PA 0, RB 0]]
               ]


consumeDiffPlaces :: Assertion
consumeDiffPlaces = testNotConflicting input expected
  where
    input = [ [CF 0, LB 0]
            , [CF 1, RB 0]
            ]
    expected = [ []
               , [[CF 0, LB 0]]
               , [[CF 1, RB 0]]
               , [ [CF 0, LB 0]
                 , [CF 1, RB 0]
                 ]
               ]

produceDiffPlaces :: Assertion
produceDiffPlaces = testNotConflicting input expected
  where
    input = [ [PA 0, LB 0]
            , [PA 1, RB 0]
            ]
    expected = [ []
               , [[PA 0, LB 0]]
               , [[PA 1, RB 0]]
               , [ [PA 0, LB 0]
                 , [PA 1, RB 0]
                 ]
               ]

produceConsumeDiffPlaces :: Assertion
produceConsumeDiffPlaces = testNotConflicting input expected
  where
    input = [ [PA 0, LB 0]
            , [CF 1, RB 0]
            ]
    expected = [ []
               , [[PA 0, LB 0]]
               , [[CF 1, RB 0]]
               , [ [PA 0, LB 0]
                 , [CF 1, RB 0]
                 ]
               ]

queriesSamePlace :: Assertion
queriesSamePlace = testNotConflicting input expected
  where
    input = [ [Q 0, LB 0]
            , [Q 0, RB 0]
            ]
    expected = [ []
               , [[Q 0, LB 0]]
               , [[Q 0, RB 0]]
               , [ [Q 0, LB 0]
                 , [Q 0, RB 0]
                 ]
               ]

syncCommonBoundary :: Assertion
syncCommonBoundary = testNotConflicting input expected
  where
    input = [ [Q 0, LB 0, S 0]
            , [Q 0, RB 0, S 0]
            , [PA 1, S 1]
            ]
    expected = [ []
               , [ [Q 0, LB 0, S 0] ]
               , [ [Q 0, RB 0, S 0] ]
               , [ [PA 1, S 1] ]
               , [ [Q 0, LB 0, S 0]
                 , [PA 1, S 1]
                 ]
               , [ [Q 0, RB 0, S 0]
                 , [PA 1, S 1]
                 ]
               ]

epsilonClosure :: Assertion
epsilonClosure = NFA.epsilonCloseNFA nfa @?= expected
  where
    nfa = textToNFA [ "0"
                    , "0--00->1,4"
                    , "1--01->2"
                    , "1--00->0"
                    , "2--00->3"
                    , "4--10->5"
                    , "5--00->6"
                    , "3,6"
                    ]

    expected = textToNFA [ "0"
                         , "0--00->0,1,4"
                         , "0--01->2"
                         , "0--10->5"
                         , "1--10->5"
                         , "1--00->0,1,4"
                         , "1--01->2"
                         , "2--00->3"
                         , "4--10->5"
                         , "5--00->6"
                         , "2,3,5,6"
                         ]

bisimPartRefA :: Assertion
bisimPartRefA = NFA.epsBisimEquiv nfa @?= expected
  where
    nfa = textToNFA [ "0"
                    , "0--01->1,3"
                    , "1--10->2"
                    , "3--11->4"
                    , "2,4"
                    ]

    expected :: NFA Int Int
    expected = textToNFA [ "0"
                         , "0--01->1"
                         , "0--01->3"
                         , "1--10->2"
                         , "3--11->2"
                         , "2"
                         ]

bisimPartRefB :: Assertion
bisimPartRefB = NFA.epsBisimEquiv nfa @?= expected
  where
    nfa = textToNFA [ "0"
                    , "0--10->1"
                    , "0--11->3"
                    , "1--01->2"
                    , "3--01->4"
                    , "2,4"
                    ]

    expected :: NFA Int Int
    expected = textToNFA [ "0"
                         , "0--10->1"
                         , "0--11->1"
                         , "1--01->2"
                         , "2"
                         ]

bisimPartRefC :: Assertion
bisimPartRefC = NFA.epsBisimEquiv nfa @?= expected
  where
    nfa = textToNFA [ "0"
                    , "0--00->0,1"
                    , "0--11->2"
                    , "1--11->3"
                    , "2,3"
                    ]

    expected :: NFA Int Int
    expected = textToNFA [ "0"
                         , "0--00->0,1"
                         , "0--11->2"
                         , "1--11->2"
                         , "2"
                         ]

bisimPartRefD :: Assertion
bisimPartRefD = NFA.epsBisimEquiv nfa @?= expected
  where
    nfa = textToNFA [ "0"
                    , "0--00->1,2"
                    , "1--11->3"
                    , "2--11->4"
                    , "3,4"
                    ]

    expected :: NFA Int Int
    expected = textToNFA [ "0"
                         , "0--00->1"
                         , "0--11->3"
                         , "1--11->3"
                         , "3"
                         ]

bisimPartRefE :: Assertion
bisimPartRefE = NFA.epsBisimEquiv nfa @?= expected
  where
    -- Test a tricky case for the quotienting, takes (3, [1,2]) as a
    -- quotienting partition, potentially causing problems for init states.
    nfa = textToNFA [ "3"
                    , "3--00->3,2"
                    , "2--00->2,1"
                    , "1--00->1"
                    , "1--11->0"
                    , "0"
                    ]

    expected :: NFA Int Int
    expected = textToNFA [ "1"
                         , "1--00->1"
                         , "1--11->0"
                         , "0"
                         ]

genSimRela :: Assertion
genSimRela = generateSimRel nfa 2 @?= expected
  where
    nfa = textToNFA [ "0,1"
                    , "0--01->2"
                    , "1--01->3"
                    , "2--10->4"
                    , "2--11->5"
                    , "3--11->6"
                    , "4,5,6"
                    ]

    expected = M.fromList [ (0, S.singleton 0)
                          , (2, S.singleton 2)
                          , (4, S.fromList [4,5,6])
                          , (1, S.fromList [0, 1])
                          , (3, S.fromList [2, 3])
                          , (5, S.fromList [4,5,6])
                          , (6, S.fromList [4,5,6])
                          ]

simRelBNFA :: NFA Int Int
simRelBNFA = textToNFA [ "0,3"
                       , "0--01->1"
                       , "1--10->2"
                       , "1--11->2"
                       , "3--01->4,5"
                       , "4--10->6"
                       , "5--11->7"
                       , "2,6,7"
                       ]

simRelb1Rel = M.fromList [ (0, S.singleton 0)
                         , (1, S.singleton 1)
                         , (2, S.fromList [2,6,7])
                         , (3, S.fromList [0,3])
                         , (4, S.fromList [1,4])
                         , (5, S.fromList [1,5])
                         , (6, S.fromList [2,6,7])
                         , (7, S.fromList [2,6,7])
                         ]

genSimRelb1 :: Assertion
genSimRelb1 = generateSimRel simRelBNFA 1 @?= simRelb1Rel

genSimRelb2 :: Assertion
genSimRelb2 = generateSimRel simRelBNFA 2 @?= expected
  where
    -- With lookahead 2, 3 also simulates 0.
    expected = M.insertWith S.union 0 (S.singleton 3) simRelb1Rel

genSimRelc :: Assertion
genSimRelc = generateSimRel nfa 2 @?= expected
  where
    nfa = textToNFA [ "1"
                    , "0--*->0"
                    , "1--*->1,2"
                    , "2--*->0,1,2"
                    , "2"
                    ]

    expected = M.fromList [ (0, S.fromList [0,1,2])
                          , (1, S.fromList [1,2])
                          , (2, S.fromList [2])
                          ]

genSimReld :: Assertion
genSimReld = generateSimRel nfa 2 @?= expected
  where
    nfa = textToNFA [ "1"
                    , "1--0->1"
                    , "1--1->2"
                    , "2--1->1"
                    , "2--0->2"
                    , "2--1->3"
                    , "3--0->3"
                    , "3"
                    ]

    expected = M.fromList [ (1, S.fromList [1])
                          , (2, S.fromList [2])
                          , (3, S.fromList [3])
                          ]

genSimRele :: Assertion
genSimRele = generateSimRel nfa 2 @?= expected
  where
    -- Ensure that simulation respects intermediate final states
    nfa = textToNFA [ "1"
                    , "1--*->0"
                    , "0--*->0"
                    , "0--*->1"
                    , "1"
                    ]

    expected = M.fromList [ (0, S.fromList [0])
                          , (1, S.fromList [1])
                          ]

pruneTransitions :: Assertion
pruneTransitions = res @?= expected
  where
    res = runEval . runWriterT $ prune lts rel
    rel = M.fromList [(0, S.fromList [1,2]), (1, S.fromList [2]), (2, S.empty)]

    (NFA lts _ _) = textToNFA [ "0"
                              , "0--*->0"
                              , "1--*->1,2"
                              , "2--*->0,1,2"
                              , "0"
                              ]

    (NFA exp _ _) = textToNFA [ "0"
                              , "0--*->0"
                              , "1--*->2"
                              , "2--*->2"
                              , "0"
                              ]

    expected = (exp, Any True)

getDeadStates :: Assertion
getDeadStates = res @?= expected
  where
    res = deadStates nfa

    nfa = textToNFA [ "0,9"
                    , "0--*->1,2"
                    , "2--*->5"
                    , "2--*->3"
                    , "3--*->12"
                    , "12--*->3"
                    , "1--*->3"
                    , "4--*->4"
                    , "9--*->10"
                    , "10--*->3"
                    , "10--*->11"
                    , "3"
                    ]

    expected = (False, S.fromList [4,5,11])

dontKillNonDeadStates :: Assertion
dontKillNonDeadStates = res @?= expected
  where
    res = deadStates nfa

    nfa = textToNFA [ "1"
                    , "1--*->1,2"
                    , "2--*->1,2"
                    , "2--*->0"
                    , "0--*->2"
                    , "0--*->0"
                    , "1--*->3"
                    , "3--*->1"
                    , "3--*->3"
                    , "2"
                    ]

    expected = (False, S.fromList [])

deadStatesInitIsFinal :: Assertion
deadStatesInitIsFinal = res @?= expected
  where
    res = deadStates nfa

    nfa = textToNFA [ "3"
                    , "2--1->2"
                    , "2--0->0"
                    , "0--*->1,3"
                    , "1--1->1"
                    , "1,2,3"
                    ]

    expected = (False, S.fromList [0,1,2])


canDoActions :: [Test]
canDoActions = concatMap makeTests
    [ (0,[True, True, True, True, False, True, False])
    , (1,[False, True, True, True, False, True, False])
    , (2,[False, True, True, True, False, True, False])
    , (3,[False, True, True, True, False, True, False])
    , (4,[True, True, True, True, True, True, True])
    , (5,[False, True, True, True, False, True, False])
    , (6,[False, True, True, True, False, True, True])
    ]
  where
    makeTests (p, qs) = map (makeTest p) $ zip [0..6] qs

    makeTest p (q, expect) = TestLabel (show (p, q, expect)) $ TestCase $ canDoAllActionsOf nfa p q @?= expect

    nfa = textToNFA [ "0"
                    , "0--00->1,2"
                    , "0--01->3"
                    , "4--0*->5"
                    , "4--10->6"
                    , "6--10->6"
                    , "1,2,3,5,6"
                    ]

initRelGeneration :: Assertion
initRelGeneration = initRel nfa @?= expected
  where
    expected = M.fromList [ (0, S.singleton 0)
                          , (1, S.fromList [0..4])
                          , (2, S.fromList [0,2,3])
                          , (3, S.fromList [0,3])
                          , (4, S.fromList [0,2,3,4])
                          ]

    nfa = textToNFA [ "0"
                    , "0--0*->1"
                    , "0--10->0"
                    , "0--11->2"
                    , "2--0*->2"
                    , "3--0*->3"
                    , "3--10->3"
                    , "4--0*->4"
                    , "0,2,3"
                    ]

quotientNFA :: Assertion
quotientNFA = res @?= (expected, Any True)
  where
    res = quotientByPartition partition input
    partition = S.fromList [ S.singleton 0
                           , S.fromList [1,2]
                           ]

    input = textToNFA [ "1"
                      , "0--*->0"
                      , "1--*->1,2"
                      , "2--*->0,1,2"
                      , "1,2"
                      ]

    expected = textToNFA [ "1"
                         , "0--*->0"
                         , "1--*->0,1"
                         , "1"
                         ]

quotientNFA2 :: Assertion
quotientNFA2 = res @?= (expected, Any True)
  where
    res = quotientByPartition partition input
    partition = S.fromList [ S.singleton 2
                           , S.fromList [0,1]
                           ]
    input = textToNFA [ "1"
                      , "0--*->0"
                      , "1--*->1,2"
                      , "2--*->0,1,2"
                      , "2"
                      ]

    expected = textToNFA [ "0"
                         , "0--*->0,2"
                         , "2--*->0,2"
                         , "2"
                         ]

equivalenceNFA :: Assertion
equivalenceNFA =
    assertBool "Shouldn't be equivalent!" (not $ equivalenceHKC nfa1 nfa2)
  where
    nfa1 = textToNFA [ "0"
                     , "0--000000->0"
                     , "0--000100,100000->1"
                     , "1--000001,001000->0"
                     , "1--000000,000010,0100*0->1"
                     , "0"
                     ]

    nfa2 = textToNFA[ "0"
                    , "0--000000->0"
                    , "0--010000->1"
                    , "1--100000->0"
                    , "1--00000*->1"
                    , "0--000010->2"
                    , "2--000100->0"
                    , "2--00*000->2"
                    , "0"
                    ]

mayrfig6 :: Assertion
mayrfig6 = generateSimRel nfa 2 @?= expected
  where
    expected = M.fromList [ (0, S.fromList [0,1])
                          , (1, S.fromList [0,1])
                          , (2, S.fromList [0,1,2])
                          , (3, S.fromList [0,1,3])
                          ]

    nfa = textToNFA [ "0,1"
                    , "0--*->0"
                    , "1--*->2,3"
                    , "2--0->1"
                    , "3--1->1"
                    , "0,1,2,3"
                    ]

mayrfig6B :: Assertion
mayrfig6B = generateSimRel nfa 2 @?= expected
  where
    expected = M.fromList [ (0, S.fromList [0,3])
                          , (1, S.fromList [0,1,3,4])
                          , (2, S.fromList [0,2,3,5])
                          , (3, S.fromList [0,3])
                          , (4, S.fromList [0,1,3,4])
                          , (5, S.fromList [0,2,3,5])
                          ]

    nfa = textToNFA [ "0,3"
                    , "0--*->1,2"
                    , "1--0->0"
                    , "2--1->0"
                    , "3--*->4,5"
                    , "4--0->4,5"
                    , "5--1->4,5"
                    , "0,1,2,3,4,5"
                    ]

useInterleaving :: Assertion
useInterleaving = res @?= expected
  where
    res = toNFAWithMarking True (listToMarkingList []) net
    net = mkNet 3 3 []
            [ [LB 0, RB 0]
            , [LB 1, RB 1]
            , [LB 2, RB 2]
            ]


    expected = textToNFAWB [ "0"
                           , "0--000/000,100/100,010/010,001/001->0"
                           , "0"
                           ]

toNFA1 :: Assertion
toNFA1 = res @?= expected
  where
    res = toNFAWithMarking False (listToMarkingList [DontCare]) net

    net = mkNet 1 2 [Absent]
            [ [LB 0, CF 0, PA 0, RB 0]
            , [LB 0, RB 1]
            , [PA 0, RB 0, RB 1]
            ]

    expected = textToNFAWB [ "1"
                           , "1--0/00,1/01->1"
                           , "1--0/11->0"
                           , "0--0/00,1/01->0"
                           , "0,1"
                           ]

toNFA2 :: Assertion
toNFA2 = res @?= expected
  where
    res = toNFAWithMarking False (listToMarkingList [DontCare]) net

    net = mkNet 0 5 [Present]
            [ [CF 0, RB 0]
            , [RB 0, RB 1]
            , [RB 2, RB 3, RB 4]
            ]

    expected = textToNFAWB [ "0"
                           , "0--/00000,/00111,/11000,/11111->0"
                           , "0--/10000,/10111->1"
                           , "1--/00000,/00111,/11000,/11111->1"
                           , "0,1"
                           ]
toNFA3 :: Assertion
toNFA3 = res @?= expected
  where
    res = toNFAWithMarking False (listToMarkingList [DontCare]) net

    net = mkNet 1 5 [Present]
            [ [LB 0, CF 0, RB 0]
            , [LB 0, RB 0, RB 1]
            , [LB 0, RB 2, RB 3, RB 4]
            ]

    expected = textToNFAWB [ "0"
                           , "0--0/00000,1/00111,1/11000->0"
                           , "0--1/10000->1"
                           , "1--0/00000,1/00111,1/11000->1"
                           , "0,1"
                           ]


doTypeCheck input nameMap expectedOr = (parse >>= tyCheck) @?= expectedOr
  where
    parse = do
        expr <- parseRawExpr (T.unlines input)
        let wiringDef = WiringDefinition usedImports expr
            noComponents = ComponentsAndWiring [] wiringDef
        fst <$> lookupNames (`M.lookup` M.fromList nameMap) noComponents

    usedImports = map fst nameMap

    tyCheck e = either (Left . show) Right (checkType id e)

typeChecking1 :: Assertion
typeChecking1 = doTypeCheck input nameMap expectedOr
  where
    input = [ "bind foo = n in"
            , "(\\x : Net 2 2 . x ; foo) (foo ; foo)"
            ]
    nameMap = [("n", (2,2))]
    expectedExpr = EBind (EPreComputed (2,2))
                         (EApp (ELam (ESeq (EVar (VarId 0)) (EVar (VarId 1))))
                               (ESeq (EVar (VarId 0)) (EVar (VarId 0))))

    expectedOr = Right (expectedExpr, TyArr 2 2)

-- data BinOp = Add
--            | Sub
--            deriving (Eq, Show)
--
-- newtype VarId = VarId { varToInt :: Int }
--               deriving (Eq, Ord, Show)
--
-- -- 'Expr p' contains precomputed values of type @p@.
-- data Expr p = EVar VarId
--             | ENum Int
--             | ERead
--             | EIntCase (Expr p) (Expr p) (Expr p)
--             | EBin BinOp (Expr p) (Expr p)
--             | EConstant InterleavingMarkedNet
--             | EPreComputed p
--             | EApp (Expr p) (Expr p)
--             | ELam (Expr p)
--             | EBind (Expr p) (Expr p)
--             | EFold (Expr p) (Expr p) (Expr p)
--             | ESeq (Expr p) (Expr p)
--             | ETen (Expr p) (Expr p)
--             deriving (Eq, Show, Functor, Foldable, Traversable)
--
--data Value m p = VLam (Value m p -> m (Value m p))
--               | VBase p
--               | VInt Int
--
--exprEval :: forall r m . (Functor m, Monad m, MonadFix m)
--         => (InterleavingMarkedNet -> m r)
--         -> (r -> r -> m (Value m r))
--         -> (r -> r -> m (Value m r))
--         -> (m Int)
--         -> Expr r -> m (Value m r)

instance Eq r => Eq (Value m r) where
    (VBase p) == (VBase q) = p == q
    (VInt i) == (VInt j) = i == j
    _ == _ = False


addEvalLeet = exprEval (const . return $ 1337) add add getParam
  where
    getParam = return 0
    add = (\x y -> return $ VBase (x + y))

evalRecFunction :: Assertion
evalRecFunction = runIdentity (addEvalLeet expr) @?= VBase 3
  where
    -- bind f = \x . intcase x 0 (\p . 1 ; p)
    -- in f 3
    expr = EBind bind body
    bind = ELam (EIntCase
                    (EVar (VarId 0))
                    (EPreComputed 0)
                    (ELam (ESeq (EPreComputed 1) (EVar (VarId 0)))))
    body = EApp (EVar (VarId 0)) (ENum 3)

evalUnusedBind :: Assertion
evalUnusedBind = runIdentity (addEvalLeet expr) @?= VBase 10
  where
    expr = EBind (ELam (EVar (VarId 0))) (EPreComputed 10)

simpleDotNet :: Assertion
simpleDotNet = (toDot <$> toStringTestNet) @?= Just expected
  where
    toDot = llNet2Dot (listToMarkingList []) . net2LLNet
    expected = unlines
        [ "digraph SomeName {"
        , "node [shape = circle];"
        , "p1 [ label=\"p1\" ];"
        , "p2 [ color=blue label=\"p2\" ];"
        , "node [style=filled,fillcolor=grey82,shape = box];"
        , "t1 [label=\"t1\"];"
        , "t2 [label=\"t2\"];"
        , "\"p2\" -> \"t1\" ;"
        , "\"t1\" -> \"p1\" ;"
        , "\"p1\" -> \"t2\" ;"
        , "\"t2\" -> \"p2\" ;"
        , "}"
        ]

toStringTestNet = Nets.compose opbs eps >>= Nets.compose eta
  where
    opbs = Nets.tensor opbLR opbRL

    opbLR = mkNet 1 1 [Absent]
        [ [LB 0, PA 0]
        , [CF 0, RB 0]
        ]

    opbRL = mkNet 1 1 [Present]
        [ [LB 0, CF 0]
        , [PA 0, RB 0]
        ]

    eta = mkNet 0 2 [] [ [RB 0, RB 1] ]

    eps = mkNet 2 0 [] [ [LB 0, LB 1] ]

simpleLOLANet :: Assertion
simpleLOLANet =
    (unparseLOLANet (listToMarkingList []) . net2LOLANet <$> toStringTestNet)
    @?= Just expected
  where
    expected = unlines
        [ "PLACE SAFE : P0, P1;"
        , "MARKING P1 : 1;"
        , "TRANSITION T0"
        , "CONSUME P1 : 1;"
        , "PRODUCE P0 : 1;"
        , "TRANSITION T1"
        , "CONSUME P0 : 1;"
        , "PRODUCE P1 : 1;"
        , "ANALYSE MARKING "
        ]
