import Control.Arrow ( (***) )
import qualified Data.IntMap as IM
import Data.Set ( Set )
import qualified Data.Set as S
import Test.Framework ( defaultMain, testGroup )
import Test.Framework.Providers.HUnit ( testCase )
import Test.HUnit ( Assertion, (@?=) )

import MTBDD
import MTBDD.Internals

import Prelude hiding ( (||), (**) )

main :: IO ()
main = defaultMain
    [ testGroup "Construction"
        [ testCase "unit with Vars" testUnitWithVars
        , testCase "constant" testConstant
        ]
    , testGroup "Union"
        [ testCase "shared leaf" testSharedLeaf
        , testCase "distinct vars" testDistinctVars
        ]
    , testGroup "Cross Product"
        [ testCase "cross" testCross
        ]
    ]

-- Constructs a MTBDD from a list of paths, where a path is a sequence of
-- variable assignments and a value. This is specialised to set-valued BDDs,
-- that is, MTBDDs.
fromPaths :: (Ord v, Ord e, Eq e) => [([(v, Bool)], Set e)] -> MTBDD v (Set e)
fromPaths = foldr1 (||) . map (uncurry (unitWithVars S.empty))

testUnitWithVars :: Assertion
testUnitWithVars = res @?= expected
  where
    res = unitWithVars 0 [(0, True), (1, False), (2, True)] 10
    expected :: MTBDD Int Int
    expected = MTBDD eTop eData

    eTop = 4
    eNodes = IM.fromList [ (0, Leaf 0)
                         , (1, Leaf 10)
                         , (2, Branch 2 0 1)
                         , (3, Branch 1 2 0)
                         , (4, Branch 0 0 3)
                         ]

    eData = (eNodes, S.fromList [0,10])

testConstant :: Assertion
testConstant = res @?= expected
  where
    res :: MTBDD Int Int
    res = constant 42
    expected :: MTBDD Int Int
    expected = MTBDD 0 (IM.singleton 0 (Leaf 42), S.singleton 42)

testSharedLeaf :: Assertion
testSharedLeaf = res @?= expected
  where
    res = fromPaths [ ([(0, False), (1, False)], S.singleton 0)
                    , ([(0, False), (1, True)], S.singleton 1)
                    , ([(0, True), (1, False)], S.singleton 1)
                    , ([(0, True), (1, True)], S.singleton 2)
                    ]

    expected :: MTBDD Int (Set Int)
    expected = MTBDD eTop eData

    eTop = 5
    eNodes = IM.fromList [ (0, Leaf $ S.singleton 0)
                         , (1, Leaf $ S.singleton 1)
                         , (2, Branch 1 0 1)
                         , (3, Leaf $ S.singleton 2)
                         , (4, Branch 1 1 3)
                         , (5, Branch 0 2 4)
                         ]

    eData = (eNodes, S.fromList $ map S.singleton [0,1,2])

testDistinctVars :: Assertion
testDistinctVars = (bdd1 || bdd2) @?= expected
  where
    bdd1 = fromPaths [ ([(0, False), (2, False)], S.singleton 0)
                     , ([(0, False), (2, True)], S.singleton 1)
                     , ([(0, True),  (2, False)], S.singleton 2)
                     , ([(0, True),  (2, True)], S.singleton 3)
                     ]

    bdd2 = fromPaths [ ([(1, False)], S.singleton 4)
                     , ([(1, True)],  S.singleton 5)
                     ]

    expected :: MTBDD Int (Set Int)
    expected = MTBDD eTop eData

    eTop = 14
    eNodes = IM.fromList [ (0, Leaf $ S.fromList [0,4])
                         , (1, Leaf $ S.fromList [1,4])
                         , (2, Branch 2 0 1)

                         , (3, Leaf $ S.fromList [0,5])
                         , (4, Leaf $ S.fromList [1,5])
                         , (5, Branch 2 3 4)

                         , (6, Branch 1 2 5)

                         , (7, Leaf $ S.fromList [2,4])
                         , (8, Leaf $ S.fromList [3,4])
                         , (9, Branch 2 7 8)

                         , (10, Leaf $ S.fromList [2,5])
                         , (11, Leaf $ S.fromList [3,5])
                         , (12, Branch 2 10 11)

                         , (13, Branch 1 9 12)

                         , (14, Branch 0 6 13)
                         ]

    eData = (eNodes, eVals)
    eVals = S.fromList . map S.fromList $
        [[0,4],[0,5],[1,4],[1,5],[2,4],[2,5],[3,4],[3,5]]

testCross :: Assertion
testCross = (bdd1 ** bdd2) @?= expected
  where
    bdd1 = fromPaths [ ([(0, False), (2, False)], S.singleton 0)
                     , ([(0, False), (2, True)], S.singleton 1)
                     , ([(0, True),  (2, False)], S.singleton 2)
                     , ([(0, True),  (2, True)], S.singleton 3)
                     ]

    bdd2 = fromPaths [ ([(1, False)], S.singleton 4)
                     , ([(1, True)],  S.singleton 5)
                     ]

    expected :: MTBDD Int (Set Int, Set Int)
    expected = MTBDD eTop eData

    mkLeaf l r = Leaf $ (S.fromList l, S.fromList r)

    eTop = 14
    eNodes = IM.fromList [ (0, mkLeaf [0] [4])
                         , (1, mkLeaf [1] [4])
                         , (2, Branch 2 0 1)

                         , (3, mkLeaf [0] [5])
                         , (4, mkLeaf [1] [5])
                         , (5, Branch 2 3 4)

                         , (6, Branch 1 2 5)

                         , (7, mkLeaf [2] [4])
                         , (8, mkLeaf [3] [4])
                         , (9, Branch 2 7 8)

                         , (10, mkLeaf [2] [5])
                         , (11, mkLeaf [3] [5])
                         , (12, Branch 2 10 11)

                         , (13, Branch 1 9 12)

                         , (14, Branch 0 6 13)
                         ]

    eData = (eNodes, eVals)
    eVals = S.fromList . map (S.fromList *** S.fromList) $
        [([0],[4]),([0],[5]),([1],[4]),([1],[5]),([2],[4]),([2],[5]),([3],[4]),([3],[5])]
