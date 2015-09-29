module LOLANets where

import Data.List ( intercalate )
import Data.Maybe ( mapMaybe )

import Marking ( WildCardMarking, WildCardMarks(..), markingListToList )
import Util ( unlines )

import Prelude hiding ( unlines )

data LOLANet = LOLANet [String] [String] [(String, [String], [String])]
             deriving ( Eq, Show )

unparseLOLANet :: WildCardMarking -> LOLANet -> String
unparseLOLANet wantedMarking (LOLANet places marked transitions) =
    unlines [ unparsePlaces places
            , unparseMarking marked
            , unlines . map unparseTransition $ transitions
            , unparseWantedMarking . zip [(0 :: Int)..] $
                markingListToList wantedMarking
            ]
  where
    toPlace = ("P" ++) . show
    unparsePlaces ps = "PLACE SAFE : " ++ intercalate ", " ps ++ ";"

    unparseMarking ps = "MARKING " ++ unparsePlaceMarkings ps ++ ";"

    unparseTransition (name, consumes, produces) =
        unlines [ "TRANSITION " ++ name
                , "CONSUME " ++ unparsePlaceMarkings consumes ++ ";"
                , "PRODUCE " ++ unparsePlaceMarkings produces ++ ";"
                ]

    unparsePlaceMarkings ps = intercalate ", " . map (++ " : 1") $ ps

    unparseWantedMarking ps = "ANALYSE MARKING "
        ++ intercalate ", " (mapMaybe toWantedMarking ps)

    toWantedMarking (i, wc) = case wc of
        Yes -> Just $ toPlace i ++ " : 1"
        No -> Just $ toPlace i ++ " : 0"
        _ -> Nothing

