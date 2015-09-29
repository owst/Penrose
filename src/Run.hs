{-# LANGUAGE TupleSections #-}
module Run where

import Control.Arrow ( first )
import Control.Applicative ( (<$>) )
import Control.DeepSeq ( NFData(..) )
import Control.Monad ( filterM )
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.Maybe ( MaybeT, runMaybeT )
import Data.IORef ( newIORef, IORef, readIORef, writeIORef )
import Data.Map.Strict ( Map )
import qualified Data.Map as M ( fromList, lookup )
import Data.Maybe ( fromMaybe )
import qualified Data.Text as T
import qualified Data.Text.IO as DTIO
import Safe ( readMay )
import System.Directory ( doesFileExist, doesDirectoryExist
                        , getDirectoryContents )
import System.FilePath ( (</>), takeExtension, dropExtension, takeFileName
                       , takeDirectory )
import System.PosixCompat.Files ( isRegularFile, getFileStatus )

import DSL.ComponentsAndWiringParser ( parseComponentsAndWiring
                                     , parseNetDefinition )
import DSL.Expr ( checkType, Type(..) )
import DSL.ProcessParse ( lookupNames, netDefinitionToMarkedNet )
import ParseNFA ( textToNFAWB )
import LOLANets ( unparseLOLANet )
import Nets ( NetWithBoundaries(..), net2LLNet, net2LOLANet, MarkedNet
            , net2LLNetWithReadArcs )
import PEPReadArcs ( unparseLLNetWithReadArcs )
import PEP ( unparseLLNet, llNet2Dot, llNet2PNML )
import NFA ( nfaWB2Dot, nfaWB2NFAOutput, NFAWithBoundaries(..)
           , toNFAWithMarking )
import Util ( timeIO, failError, (.:), pretty )
import ProcessExpr

-- TODO: we should really separate the output type from the computation type
data OutputType = Mono_UnminNFA
                | Mono_RawNet
                | Mono_PNML
                | Mono_LLNet
                | Mono_LLNetReadArcs
                | Mono_LLNetDot
                | Mono_LOLANet
                | Comp_NFA
                | Comp_NFASlow
                | Comp_NFADot
                deriving (Read, Show)

outputTypeDoc :: OutputType -> String
outputTypeDoc outType = header ++ "\n" ++ detail ++ ".\n"
  where
    (header, detail) = case outType of
        Mono_UnminNFA -> (monoStr, "Reachability graph, unminimised")
        Mono_RawNet -> (monoStr, "Composite net, internal format")
        Mono_PNML -> (monoStr, "Composite net, PNML format")
        Mono_LLNet -> (monoStr, "Composite net, ll_net format")
        Mono_LLNetReadArcs ->
            (monoStr, "Composite net, cunf ll_net format with read arcs")
        Mono_LLNetDot ->
            (monoStr, "Composite net, DOT format, showing structure")
        Mono_LOLANet -> (monoStr, "Composite net, LOLA format")
        Comp_NFA -> (compStr, "NFA format, used to import pre-computed NFAs "
                              ++ "for commonly used components")
        Comp_NFASlow -> (compStr, "DOT format representation of resulting "
                                 ++ "(reduced) NFA, using naive (slow) algorithm")
        Comp_NFADot -> (compStr, "DOT format representation of resulting "
                                 ++ "(reduced) NFA")
    monoStr = "Monolithic: flatten wiring decomposition to composite "
              ++ "net, before output."
    compStr = "Compositional: traverse wiring decomposition, converting to "
              ++ "output,\nexploiting memoisation and language-equivalence."

data RunResult = NFAResult (String, (Counters, Sizes))
               | NFASlowResult (String, SlowCounters)
               | NWBResult String
               | RawResult String
               deriving Show

instance NFData RunResult where
    rnf (NFAResult x) = rnf x
    rnf (NFASlowResult x) = rnf x
    rnf (NWBResult x) = rnf x
    rnf (RawResult x) = rnf x

runner :: OutputType -> FilePath -> Maybe [Int] -> IO (RunResult, Double)
runner outputType file mbParams = do
    exists <- doesFileExist file
    if not exists
        then failError $ "input file: " ++ file ++ " doesn't exist!"
        else do
            input <- DTIO.readFile file
            ref <- newIORef (fromMaybe [] mbParams)
            let getP = promptForParam ref
            (\f -> f input getP) $ case outputType of
                Mono_LLNet -> goNet toLLNet
                Mono_LLNetReadArcs -> goNet toLLNetWithReadArcs
                Mono_PNML -> goNet toPNML
                Mono_LLNetDot -> goNet toLLDot
                Mono_LOLANet -> goNet toLOLANet
                Mono_RawNet -> goRaw toRawNet
                Mono_UnminNFA -> goRaw toRawNFADot
                Comp_NFA -> goNFA nfaWB2NFAOutput
                Comp_NFASlow -> goNFASlow nfaWB2Dot
                Comp_NFADot -> goNFA nfaWB2Dot
  where
    libDir = takeDirectory file </> "lib"

    toPNML marking = llNet2PNML marking . net2LLNet
    toLLNet marking = unparseLLNet marking . net2LLNet
    toLLNetWithReadArcs marking =
        unparseLLNetWithReadArcs marking . net2LLNetWithReadArcs
    toLLDot marking = llNet2Dot marking . net2LLNet
    toLOLANet marking = unparseLOLANet marking . net2LOLANet
    toRawNet m = (++ "\nWanted Marking: " ++ pretty m) . pretty
    toRawNFADot = nfaWB2Dot .: toNFAWithMarking False

    goNet fmt input getP = runWith (findLibraryNWBs libDir) getNetBounds input $
        doOutput NWBResult (uncurry fmt) (expr2NWB getP)
    goNFASlow fmt input getP =
        runWith (findLibraryNFAs libDir) getNFABounds input $
            doOutput NFASlowResult (first fmt) (expr2NFASlow getP)
    goNFA fmt input getP = runWith (findLibraryNFAs libDir) getNFABounds input $
        doOutput NFAResult (first fmt) (expr2NFA getP)
    goRaw fmt input getP = runWith (findLibraryNWBs libDir) getNetBounds input $
        doOutput RawResult (uncurry fmt) (expr2NWB getP)

    doOutput toRes format convert =
        timeIO . ((toRes . format) <$>) . convert

    getNetBounds (_, NetWithBoundaries l r _ _ _ _) = (l, r)

    getNFABounds (NFAWithBoundaries _ l r) = (l, r)

    runWith getLib getBounds input outputter = do
        lib <- getLib
        let lookupImport name = lib >>= M.lookup name
            compAndWiring = parseComponentsAndWiring input
            renamed = compAndWiring >>= lookupNames lookupImport
        case renamed of
            Left err -> failError $ "couldn't parse: " ++ err
            Right (expr, _) -> do
                let exprType = checkType getBounds expr
                case exprType of
                    Left err -> failError $ "Couldn't typecheck: "
                                                ++ show err
                    Right (expr', TyArr _ _) -> outputter expr'
                    Right ty -> failError $
                        "Top-level expr must be base type, got: "++ show ty

type LibraryMap p = Map String p

findLibraryNFAs :: FilePath -> IO (Maybe (LibraryMap (NFAWithBoundaries Int)))
findLibraryNFAs libDir = findThings libDir "nfa" (textToNFAWB . T.lines)

findLibraryNWBs :: FilePath -> IO (Maybe (LibraryMap MarkedNet))
findLibraryNWBs libDir = findThings libDir "nwb" $ \input ->
    either error snd $ parseNetDefinition input >>= netDefinitionToMarkedNet

findThings :: FilePath -> String -> (T.Text -> t) -> IO (Maybe (LibraryMap t))
findThings libDir extension parseThing = runMaybeT $ do
    files <- getLibraryContents libDir
    let things = filter ((== ('.' : extension)) . takeExtension) files
        getter n = do
            thing <- lift $ (parseThing <$>) . DTIO.readFile $ n
            return (toFileName n, thing)
    M.fromList <$> mapM getter things

toFileName :: FilePath -> FilePath
toFileName = dropExtension . takeFileName

getLibraryContents :: FilePath -> MaybeT IO [FilePath]
getLibraryContents dir = do
    exists <- lift $ doesDirectoryExist dir
    if not exists
        then fail "missing lib dir"
        else lift $ do
            contents <- map (dir </>) <$> getDirectoryContents dir
            filterM ((isRegularFile <$>) . getFileStatus) contents

promptForParam :: IORef [Int] -> IO Int
promptForParam ref = do
    is <- readIORef ref
    case is of
        [] -> getInt
        (x:xs) -> writeIORef ref xs >> return x
  where
    getInt :: IO Int
    getInt = do
        putStrLn "Enter a number for PARAM"
        line <- getLine
        case readMay line of
            Just x -> return x
            Nothing -> putStrLn "Invalid number, try again!" >> getInt

