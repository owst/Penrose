module Benches where

import Data.List ( isPrefixOf )
import System.FilePath ( (</>) )

type BenchSize = [Int]

toExamplePath :: String -> FilePath
toExamplePath f = "examples" </> (f ++ ".netdecomp")

goodSizes :: [BenchSize]
goodSizes = map (return . (2^)) ([1,3,5,9,12,15] :: [Int])
badSizes :: [BenchSize]
badSizes = map return [2, 4, 8, 10, 13, 16]
conTreeSizes :: [BenchSize]
conTreeSizes = disTreeSizes ++ [[7, 7]]
disTreeSizes :: [BenchSize]
disTreeSizes = map (\x -> [x,x]) [1..6]

nfaBenches :: [((String, Bool), ([BenchSize], Bool))]
nfaBenches = [ (("over",             True),  (goodSizes, False))
             , (("dac",              False), (goodSizes, False))
             , (("philo",            False), (goodSizes, True))
             , (("buffer",           False), (goodSizes, True))
             , (("replicator",       False), (goodSizes, True))
             , (("iterated_choice",  False), (goodSizes, True))
             , (("hartstone",        False), (badSizes, False))
             , (("token_ring",       False), (badSizes, False))
             , (("cyclic",           False), (badSizes, True))
             , (("counter",          True),  (badSizes, True))
             , (("conjunction_tree", False), (conTreeSizes, True))
             , (("disjunction_tree", False), (disTreeSizes, True))
             -- , ("rw", ([1,2..10], False))
             ]

doFilter :: [String] -> [((String, a), b)] -> [((String, a), b)]
doFilter [] benches = benches
doFilter wanted benches = filter (filterBench wanted) benches
  where
    filterBench names cand = any (`isPrefixOf` (fst . fst) cand) names

