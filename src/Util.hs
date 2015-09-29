module Util where

import Control.DeepSeq ( NFData(rnf) )
import Data.List ( intercalate )
import System.CPUTime ( getCPUTime )
import System.Exit ( exitFailure )
import System.IO ( hPutStrLn, stderr )
import Prelude hiding ( unlines )

timeIO :: (NFData a) => IO a -> IO (a, Double)
timeIO action = do
    start <- getCPUTime
    res <- action
    rnf res `seq` return ()
    end <- getCPUTime
    return (res, fromIntegral (end - start) / (10 ^ (12 :: Integer)))

failError :: String -> IO t
failError err = dieWith ("Error: " ++ err)

dieWith :: String -> IO t
dieWith err = hPutStrLn stderr err >> exitFailure

unlines :: [String] -> String
unlines = intercalate "\n"

infixr 8 .:
(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(f .: g) x y = f $ g x y

class (Show a) => Pretty a where
    pretty :: a -> String
    pretty = show

indentLines :: [String] -> String
indentLines = unlines . map (replicate 4 ' ' ++)
