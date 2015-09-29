{-# LANGUAGE TemplateHaskell #-}
module Main where

import Control.Applicative ( (<$>) )
import Control.Arrow ( (&&&) )
import Control.Monad ( unless )
import Language.Haskell.TH ( reify, Con(NormalC), Dec(DataD), nameBase
                           , Exp(LitE, AppE, VarE, ListE, ConE, TupE)
                           , Lit(StringL), Info(TyConI), mkName )

import Data.List ( intercalate, delete )
import Safe ( readMay )
import System.Environment ( getArgs, getProgName )
import Text.Printf ( printf )

import Run ( runner, OutputType, RunResult(..), outputTypeDoc )
import Util ( dieWith, indentLines )
import ProcessExpr ( Counters(..), StrictTriple(..), StrictQuad(..)
                   , SlowCounters(..), MaxComp(..) )

main :: IO ()
main = do
    (nonQuietArgs, isQuiet) <- processArgs <$> getArgs
    case nonQuietArgs of
        (output : file : rest) -> do
            outputType <- parseOutputType output
            let go as q = runner outputType file as >>= printRes q
            case rest of
                [] -> go Nothing isQuiet
                as -> do
                    let nums = map read as
                    if null nums
                        then go Nothing isQuiet
                        else go (Just nums) isQuiet
        _ -> printUsage
  where
    indent = ("    " ++)

    silentFlag = "-s"
    processArgs = delete silentFlag &&& (silentFlag `elem`)

    parseOutputType :: String -> IO OutputType
    parseOutputType input = case readMay input of
        Nothing -> fail $ "Couldn't parse " ++ outputTypes ++ " " ++ input
        Just r -> return r

    printRes quiet (RawResult res, time) = do
        putStrLn res
        unless quiet $
            putStrLn $ unlines [ ""
                               , "Time:"
                               , indent $ printf "%3fs" time
                               ]
    printRes quiet (NWBResult res, time ) = do
        putStrLn res
        unless quiet $
            putStrLn $ unlines [ ""
                               , "Time:"
                               , indent $ printf "%3fs" time
                               ]
    printRes quiet ( NFAResult ( res
                               , ( Counters (StrictTriple net2nfa nfa neither)
                                            (StrictQuad compYes compNo tenYes tenNo)
                                 , (net2nfas, nfas, binops)
                                 )
                               )
                   , time
                   ) = do
        putStrLn res
        unless quiet $
            putStrLn $ unlines [ ""
                               , "Time:"
                               , indent $ printf "%3fs" time
                               , ""
                               , "Counters:"
                               , indent $ show net2nfa ++ " net2NFA hits,"
                               , indent $
                                     show nfa ++ " language equivalent known NFAs,"
                               , indent $ show neither ++ " unknown Net/NFAs."
                               , ""
                               , indent $
                                    show (compYes, tenYes)
                                    ++ " known (;/*) op & args ("
                                    ++ show (compYes + tenYes) ++ " total),"
                               , indent $
                                    show (compNo, tenNo)
                                    ++ " unknown (;/*) op & args ("
                                    ++ show (compNo + tenNo) ++ " total)."
                               , ""
                               , "Cache:"
                               , indent $ show net2nfas ++ " recorded net2NFA,"
                               , indent $ show nfas ++ " unique language NFAs,"
                               , indent $ show binops ++ " Binary op triples."
                               ]
    printRes quiet ( NFASlowResult
                         ( res
                         , SlowCounters leaves seqs tens (MaxComp (_, sizes))
                         )
                   , time
                   ) = do
        putStrLn res
        unless quiet $
            putStrLn $ unlines [ ""
                               , "Time:"
                               , indent $ printf "%3fs" time
                               , ""
                               , "Counters:"
                               , indent $ show leaves ++ " leaf conversions,"
                               , indent $ show seqs
                                            ++ " sequential 2-NFA compositions,"
                               , indent $ show tens
                                            ++ " tensor 2-NFA compositions,"
                               , indent $ "Max (intermediate) 2-NFA composition state counts: "
                                            ++ show sizes
                               ]

outputTypes :: String
outputTypes = $(do
        ty <- reify ''OutputType
        let showCon (NormalC n _) = nameBase n
            showCon _ = error "Can't handle non-normal constructors"
            strs = case ty of
                        (TyConI (DataD _ _ _ cons _)) -> map showCon cons
                        _ -> error "Can't handle non-tycon type"
        return . LitE . StringL $ intercalate "|" strs)

outputDescriptions :: [(String, String)]
outputDescriptions = $(do
        ty <- reify ''OutputType
        let showCons n = AppE (VarE (mkName "show")) (ConE n)
            getDoc n = AppE (VarE (mkName "Run.outputTypeDoc")) (ConE n)
        let showCon (NormalC n _) = TupE [showCons n, getDoc n]
            showCon _ = error "Can't handle non-normal constructors"
            strs = case ty of
                        (TyConI (DataD _ _ _ cons _)) -> map showCon cons
                        _ -> error "Can't handle non-tycon type"
        return $ ListE strs)

printUsage :: IO ()
printUsage = do
    progName <- getProgName
    let mkDesc (name, desc) =
            "\n" ++ name ++ ":\n" ++ (indentLines . lines) desc
    let descStr = map mkDesc outputDescriptions
    dieWith $
        "Usage: " ++ progName ++ " " ++ outputTypes
        ++ " input_filepath [-s] [PARAM value]\n"
        ++ "\nOutput Descriptions:"
        ++ (indentLines . lines . indentLines) descStr
        ++ "\n\nIf -s is given, only output value is printed, no stats."

