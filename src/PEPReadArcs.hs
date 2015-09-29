module PEPReadArcs where

import Nets ( LLNetWithReadArcs(..) )
import Marking ( WildCardMarking )
import PEP ( unparseLLNet )
import PEPParser ( LLNet, TransID(..), PlaceID(..) )

unparseLLNetWithReadArcs :: WildCardMarking -> LLNetWithReadArcs -> String
unparseLLNetWithReadArcs marking (LLNetWithReadArcs llNet readArcs) =
    insertedBeforeLastLine
  where
    insertedBeforeLastLine = unlines $ foldr folder [] unParsedLLNetLines
    folder x [m] = x : [readArcsStr, m]
    folder x ls = x : ls

    unParsedLLNetLines = lines $ unparseLLNet marking llNet
    readArcsStr = unlines . ("RA" :) $ map toArcStr readArcs
    toArcStr (TransID i, PlaceID j) = show i ++ "<" ++ show j

