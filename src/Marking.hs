module Marking
    (
      -- ^ General types
      TokenStatus(..)
    , Marking
    , WildCardMarks(..)
    , WildCardMarking
      -- ^ General functions
    , listToMarkingList
    , concatMarkingList
    , sizeMarkingList
    , markingListToList
      -- ^Specific functions
    , wildCardMatchesMarking
    , setAtIndices
    , eqAtIndices
    ) where

import qualified Data.DList as DL
import Data.List ( intercalate )
import Data.IntSet ( IntSet )
import qualified Data.IntSet as IS

import Util ( Pretty(..) )

data MarkingList e = MarkingList !Int !(DL.DList e)
                   deriving ( Eq, Ord, Show )

instance (Pretty e) => Pretty (MarkingList e) where
    pretty m =
        intercalate ", " $
            zipWith (curry prettyNumPair) [0..] (markingListToList m)
      where
        prettyNumPair (i, t) = show (i :: Int) ++ ":" ++ pretty t

listToMarkingList :: [a] -> MarkingList a
listToMarkingList l = MarkingList (length l) (DL.fromList l)

concatMarkingList :: MarkingList a -> MarkingList a -> MarkingList a
concatMarkingList (MarkingList l1 m1) (MarkingList l2 m2) =
    MarkingList (l1 + l2) $ m1 `DL.append` m2

sizeMarkingList :: MarkingList a -> Int
sizeMarkingList (MarkingList l _) = l

markingListToList :: MarkingList a -> [a]
markingListToList (MarkingList _ dl) = DL.toList dl

data TokenStatus = Present
                 | Absent
                 deriving (Eq, Ord, Show)

instance Pretty TokenStatus where
    pretty Present = "▣"
    pretty Absent = "▢"

data WildCardMarks = DontCare
                   | No
                   | Yes
                   deriving (Eq, Enum, Ord, Show)

instance Pretty WildCardMarks where
    pretty DontCare = "*"
    pretty Yes = "▣"
    pretty No = "▢"

type WildCardMarking = MarkingList WildCardMarks

wildCardMatchesMarking :: WildCardMarking -> Marking -> Bool
wildCardMatchesMarking (MarkingList i x) (MarkingList j y) =
    if i /= j
        then error "WildCardMarking and Marking different sizes!"
        else check (DL.toList x) (DL.toList y)
  where
    check [] [] = True
    check (wc : wcs) (m : ms) = checkMatch wc m && check wcs ms
    check _ _ = error "uncaught uneven marking lists"

    checkMatch Yes Present = True
    checkMatch No Absent = True
    checkMatch DontCare _ = True
    checkMatch _ _ = False
{-# INLINE wildCardMatchesMarking #-}

type Marking = MarkingList TokenStatus

setAtIndices :: TokenStatus -> Marking -> IntSet -> Marking
setAtIndices status (MarkingList l m) set =
    MarkingList l . DL.fromList $ zipWith (curry setter) [0..] (DL.toList m)
  where
    setter (i, x) = if i `IS.member` set then status else x
{-# INLINE setAtIndices #-}

eqAtIndices :: TokenStatus -> Marking -> IntSet -> Bool
eqAtIndices status (MarkingList _ m) set = all check $ zip [0..] (DL.toList m)
  where
    check (i, x) = not (i `IS.member` set) || (x == status)
