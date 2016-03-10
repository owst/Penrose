{-# LANGUAGE TupleSections, TemplateHaskell, CPP #-}
module Benchmark where

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative ( (<$>) )
#endif

import Language.Haskell.TH ( reify, Con(NormalC), Dec(DataD), nameBase
                           , Exp(LitE), Lit(StringL), Info(TyConI) )

import Control.Arrow ( (***), (&&&) )
import Control.Monad ( liftM2, forM_ )
import Data.Maybe ( fromJust )
import Data.Semigroup ( Semigroup(..) )
import Data.List ( intercalate, isPrefixOf )
import Data.List.Split ( splitOn )
import Data.List.NonEmpty ( fromList )
import Data.Time.Clock ( getCurrentTime )
import Data.Time.Format ( formatTime )
import Data.Time.Locale.Compat ( defaultTimeLocale )
import Safe ( readMay )
import System.Directory ( createDirectory, setCurrentDirectory
                        , removeDirectoryRecursive )
import System.Environment ( getArgs, getProgName )
import System.Exit ( ExitCode(..), exitFailure )
import System.IO ( hSetBuffering, stdout, BufferMode(..), stderr, hPutStrLn )
import System.Process ( readProcessWithExitCode )
import System.FilePath ( (</>) )
import Text.Printf ( printf )
import Text.Regex.PCRE.Light.Char8 ( compile, match, dotall )

import Benches ( nfaBenches, toExamplePath, doFilter, BenchSize )
import Run ( RunResult(..), runner, OutputType(..) )
import Util ( failError )

import Prelude hiding ( unlines )

unlines :: [String] -> String
unlines = intercalate "\n"

runCount :: Int
runCount = 5

data GoType = CNA
            | CLP
            | LOLA
            | MARCIE
            | TAAPL
            | PENROSE
            deriving (Read, Show, Eq)

-- Hack to delimit declaration group
$(return [])

goTypes :: String
goTypes = $(do
        ty <- reify ''GoType
        let showCon (NormalC n _) = nameBase n
            showCon _ = error "Can't handle non-normal constructors"
            strs = case ty of
                        (TyConI (DataD _ _ _ cons _)) -> map showCon cons
                        _ -> error "Can't handle non-tycon type"
        return . LitE . StringL $ intercalate "|" strs)

printUsage :: IO a
printUsage = do
    name <- getProgName
    failError $ "Usage: " ++ name ++ " " ++ goTypes ++ " [BENCHMARK_NAME]"

main :: IO ()
main = do
    args <- getArgs
    if "-h" `elem` args || "--help" `elem` args || null args
        then printUsage
        else do
            let (goTypeStr : wanted) = args
                badTypeStr = do
                    putStrLn $ "Unknown go type: " ++ goTypeStr
                    printUsage
            goType <- maybe badTypeStr return $ readMay goTypeStr
            hSetBuffering stdout NoBuffering
            let filtered = doFilter wanted nfaBenches
            ok <- trySetup goType
            if ok
                then do
                    let resFile = goTypeStr ++ "_results.tsv"
                    writeFile resFile ""
                    putStrLn "Results:"
                    forM_ filtered $ \example -> do
                        res <- showResult <$> makeExample goType example
                        putStrLn res
                        appendFile resFile (res ++ "\n")
                else do
                    putStrLnErr $ unlines
                        [ ""
                        , "FAIL!"
                        , "Could not execute a command required for benchmarks"
                        , "Make sure the reported commands are executable in"
                        , "a shell, perhaps by modifying your PATH variable"
                        ]
                    exitFailure

trySetup :: GoType -> IO Bool
trySetup goType = tryTimeAnd $ case goType of
    PENROSE -> return True
    CNA -> liftM2 (&&) (tryRun "cunf") (tryRun "cna")
    LOLA -> tryRun "lola"
    CLP -> liftM2 (&&) (tryRun "punf") (tryRun "clp")
    TAAPL -> tryRun "verifypn"
    MARCIE -> tryRun "marcie"
  where
    tryTimeAnd = liftM2 (&&) (tryRun timeBinary)
    tryRun name = do
        (ec, _, _) <- readProcessWithExitCode name [] ""
        case ec of
            (ExitFailure 127) -> do
                putStrLnErr $ concat [ "Could not execute command `"
                                     , name
                                     , "`, required to benchmark "
                                     , show goType
                                     ]
                return False
            _ -> return True

putStrLnErr :: String -> IO ()
putStrLnErr = hPutStrLn stderr

showResult :: (String, [(BenchSize, Result)]) -> String
showResult (name, countResults) = unlines $ map showCRes countResults
  where
    showCRes (count, res) = name ++ "\t" ++ show count ++ "\t" ++ show res

data FailReason = OOM
                | WrongResult
                | Inconsistent
                | TimeOut
                | CantHandleQueryPorts
                | Unknown ExitCode String String
                deriving ( Eq, Show )

type TimeMemory = (Double, Double)

data Result = OK Int Bool TimeMemory
            | Fail FailReason TimeMemory

instance Show Result where
    show (OK n _ (cTime, cMem)) =
        let nDb = fromIntegral n
        in printf "%.3f\t%.2f" (cTime / nDb) (cMem / nDb)
    show (Fail reason _) =
        let err = "FAIL: " ++ show reason
        in printf "%s\t%s" err err

instance Semigroup Result where
    (Fail lFail lTime) <> _ = Fail lFail lTime
    _ <> (Fail rFail rTime) = Fail rFail rTime
    (OK lNum lReach (lTime, lMem)) <> (OK rNum rReach (rTime, rMem))
        | lReach /= rReach = Fail Inconsistent (lTime, lMem)
        | otherwise = OK (lNum + rNum) lReach (lTime + rTime, lMem + rMem)

makeExample :: GoType -> ((String, Bool), ([BenchSize], Bool))
            -> IO (String, [(BenchSize, Result)])
makeExample goType ((name, hasQueryPort), (sizes, reachable)) =
    (name, ) . reverse <$> goExamples [] sizes
  where
    goExamples sofar [] = return sofar
    goExamples sofar (s : ss) = do
        res <- getRes
        goExamples (res : sofar) ss
      where
        goSize = (s, ) <$>
          makeSizedExample goType name hasQueryPort reachable s

        -- Only run this test size if the previous test didn't timeout/OOM
        -- (which assumes that bigger tests will also do so)
        getRes :: IO (BenchSize, Result)
        getRes = case sofar of
            [] -> goSize
            (r : _) -> case r of
                (_, Fail why timeMem)
                    | why `elem` [OOM, TimeOut] ->
                        return (s, Fail why timeMem)
                _ -> goSize

makeSizedExample :: GoType -> String -> Bool -> Bool -> BenchSize -> IO Result
makeSizedExample goType n usesQueryPorts reachable size =
    if not usesQueryPorts || goType `elem` [PENROSE, CNA]
        then do
            let which = n ++ " ~ " ++ show size
            putStrLn $ "Doing: " ++ which
            putStr $ "[1/" ++ show runCount ++ "]"
            res <- goExamples [] [1..runCount]
            putStrLn $ "\nDone: " ++ which
            return . sconcat $ fromList res
        else return $ Fail CantHandleQueryPorts (0, 0)
  where
    goExamples sofar [] = return sofar
    goExamples sofar (run : runs) = do
        res <- getRes
        goExamples (res : sofar) runs
      where
        goRun = processData <$> runExample goType n size run

        -- Only run this test size if the previous test didn't timeout/OOM
        -- (which assumes that bigger tests will also do so)
        getRes = case sofar of
            [] -> goRun
            (r : _) -> case r of
                Fail why timeMem
                    | why `elem` [OOM, TimeOut] ->
                        return $ Fail why timeMem
                _ -> goRun

    processData :: (TimeMemory,
                    Either FailReason (ExitCode, String, String)) -> Result
    processData (timeMem, Left reason) = Fail reason timeMem
    processData (timeMem, Right runData) =
        toResult reachable goType (timeMem, runData)

runExample :: GoType -> String -> BenchSize -> Int
           -> IO (TimeMemory, Either FailReason (ExitCode, String, String))
runExample goType name size run = do
    putStr $ concat ["\r[", show run, "/", show runCount, "]"]
    -- Run example test in directory named with current time
    now <- formatTime defaultTimeLocale "%Y-%m-%dT%H:%M:%S" <$>
      getCurrentTime
    let dirName = "example-run-" ++ now
    createDirectory dirName
    setCurrentDirectory dirName
    setUp goType
    res <- shellWithTimeOut
    setCurrentDirectory ".."
    removeDirectoryRecursive dirName
    return res
  where
    examplePath = ".." </> toExamplePath name

    firstLast = (init &&& last) . lines

    setUp TAAPL = do
        (NWBResult nwb) <- fst <$>
            runner Mono_PNML examplePath (Just size)
        let (pnml, marking) = firstLast nwb
            -- Turn "1 P3, 0 P2, 1 P4" into "EF(P3=1 && P2=0 && P4=1)"
            mark =
                (++ ")") .
                ("EF(" ++) .
                intercalate " && " .
                map ((\[x,y] -> y ++ "=" ++ x) .
                     splitOn " ") .
               splitOn ", " $ marking
        writeFile "marking" mark
        writeFile "input" $ unlines pnml
        writeFile "go" "verifypn input marking"
    setUp MARCIE = do
        (NWBResult nwb) <- fst <$>
            runner Mono_PNML examplePath (Just size)
        let (pnml, marking) = firstLast nwb
            -- Turn "1 P3, 0 P2, 1 P4" into "EF(P3=1 && P2=0 && P4=1)"
            mark =
                (++ ";") .
                ("EF " ++) .
                foldr1 (\x y -> concat ["[", x, " && ", y, "]"]) .
                map ((\[x,y] -> y ++ "=" ++ x) .
                     splitOn " ") .
               splitOn ", " $ marking
        writeFile "marking.ctl" mark
        writeFile "input.pnml" $ unlines pnml
        let runMarcie = "marcie --net-file=input.pnml --ctl-file=marking.ctl"
            getAns = "grep 'the formula'"
        writeFile "go" $ runMarcie ++ " | " ++ getAns
    setUp CNA = do
        (NWBResult nwb) <- fst <$>
            runner Mono_LLNetReadArcs examplePath (Just size)
        let (llNet, marking) = firstLast nwb
            -- Turn "1 P3, 0 P2, 1 P4" into ["P3", "P2", "P4"]
            cover = map (drop 2) . filter ((== '1') . head) . splitOn ", " $
                marking
        writeFile "input" $ unlines llNet
        writeFile "go" $
            "cunf input -o unfolding && cna unfolding -c " ++ unwords cover
    setUp CLP = do
        (NWBResult nwb) <- fst <$>
            runner Mono_LLNet examplePath (Just size)
        let (llNet, marking) = firstLast nwb
        writeFile "input.ll_net" $ unlines llNet
        writeFile "marking" marking
        writeFile "go"
            "punf -f=input.ll_net -m=unfolding ; clp -r marking unfolding"
    setUp LOLA = do
        (NWBResult nwb) <- fst <$>
            runner Mono_LOLANet examplePath (Just size)
        writeFile "input" nwb
        writeFile "go" "lola input"
    setUp PENROSE = writeFile "go" $
        "../dist/build/Penrose/Penrose Comp_NFA "
        ++ examplePath ++ " " ++ unwords (map show size)

matchGroups :: String -> String -> Maybe [String]
matchGroups pat str = tail <$> match (compile pat []) str []

toResult :: Bool -> GoType -> (TimeMemory, (ExitCode, String, String))
         -> Result
toResult reachable goType (timeMem, (exitCode, out, err)) =
    let partRes = case goType of
                    CNA -> cnaPartRes
                    CLP -> clpPartRes
                    LOLA -> lolaPartRes
                    PENROSE -> penrosePartRes
                    TAAPL -> taaplPartRes
                    MARCIE -> marciePartRes
    in partRes timeMem
  where

    unknown = Fail $ Unknown exitCode out err

    clpIsReachable =
        Just [] == matchGroups "the marking is reachable" out

    clpPartRes =
       case exitCode of
           ExitSuccess -> if clpIsReachable == reachable
                              then OK 1 clpIsReachable
                              else Fail WrongResult
           (ExitFailure code) -> case code of
                2 -> if not reachable
                        then OK 1 False
                        else Fail WrongResult
                _ -> unknown
    cnaSuccess =
        case matchGroups "answer\\s+:\\s(NO|YES)" out of
            Just ["NO"] -> Right False
            Just ["YES"] -> Right True
            _ -> Left unknown

    cnaPartRes = case exitCode of
        ExitSuccess ->
            case cnaSuccess of
                Right wasReach -> if wasReach == reachable
                           then OK 1 wasReach
                           else Fail WrongResult
                Left urk -> urk
        (ExitFailure _) ->
            let memStr = "cunf: No more memory" in
            if memStr `isPrefixOf` err
                then Fail OOM
                else unknown

    lolaSuccess =
        case matchGroups "state found" err of
            Just [] -> Right True
            _ -> Left unknown

    lolaPartRes = case exitCode of
        ExitSuccess -> case lolaSuccess of
            Right wasReach -> if wasReach == reachable
                           then OK 1 wasReach
                           else Fail WrongResult
            Left urk -> urk
        (ExitFailure _) ->
            let oomPat =
                    "terminate called after throwing an instance of 'overflow'"
            in case matchGroups oomPat err of
                Just [] -> Fail OOM
                _ -> case matchGroups "state is unreachable" err of
                    Just [] -> OK 1 False
                    _ -> unknown

    taaplSuccess =
        case matchGroups "Query is (?:(NOT)\\s)?satisfied" out of
            Just [] -> Just True
            Just ["NOT"] -> Just False
            _ -> Nothing

    taaplPartRes = case taaplSuccess of
            Just wasReach -> if wasReach == reachable
                           then OK 1 wasReach
                           else Fail WrongResult
            Nothing -> case matchGroups "std::bad_alloc" err of
                            Just [] -> Fail OOM
                            _ -> unknown

    marcieSuccess =
        case matchGroups "the formula is (FALSE|TRUE)" out of
            Just ["FALSE"] -> Just False
            Just ["TRUE"] -> Just True
            _ -> Nothing

    marciePartRes = case marcieSuccess of
            Just wasReach -> if wasReach == reachable
                           then OK 1 wasReach
                           else Fail WrongResult
            Nothing -> case matchGroups "memory exhausted" err of
                            Just [] -> Fail OOM
                            _ -> unknown

    penroseOutput accept = ["0", "0--/->0"] ++ ["0" | accept]

    penroseSuccess = penroseOutput reachable == take 3 (lines out)

    penrosePartRes = case exitCode of
        ExitSuccess -> OK 1 penroseSuccess
        (ExitFailure _) -> unknown

-- Assumes a shell script called "go" in the cwd
shellWithTimeOut :: IO (TimeMemory,
                        Either FailReason (ExitCode, String, String))
shellWithTimeOut = do
    res@(ec, _, _) <- go
    putStrLn "Finished go"
    timeMem <- parseTimeMem <$> readFile "timeMem"
    case ec of
        -- Timeout
        (ExitFailure 124) -> return (timeMem, Left TimeOut)
        -- OOMKilled
        (ExitFailure 137) -> return (timeMem, Left OOM)
        _ -> return (timeMem, Right res)
  where
    limit :: Int
    limit = 300 -- seconds

    go = readProcessWithExitCode timeBinary
        ["-f", "'%E %M'", "-o", "timeMem", "timeout", show limit, "bash", "go"] ""

-- A GNU compatible time binary.
timeBinary :: String
timeBinary =
    "/usr/local/bin/gtime" -- For OSX, with `brew install gnu-time`
    -- "/usr/bin/time" -- For Linux

parseTimeMem :: String -> (Double, Double)
parseTimeMem = (timeToSeconds *** mem2MB) . toComponents . fromJust . doMatch
  where
    -- The first matching group is the whole match, which we don't need, so
    -- drop it.
    doMatch s = tail <$> match (compile pattern [dotall]) s []

    pattern = "(\\d+):(\\d+).(\\d+)\\s(\\d+)"

    toComponents [m,s,ms,mem] = ((read m, read s, read ms), mem)
    toComponents cs = error $ "need 4 groups: " ++ show cs

    mem2MB = (/ 1024.0) . read

    timeToSeconds (mins, seconds, milliseconds) =
        mins * 60 + seconds + (milliseconds / 1000)
