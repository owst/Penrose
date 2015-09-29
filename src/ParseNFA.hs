module ParseNFA where

import qualified Data.Set as S
import qualified Data.Map.Strict as M

import Control.Applicative ( (<$>), (<*>), (<*) )
import Control.Monad ( when, (>=>) )
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.Either ( EitherT, hoistEither, runEitherT )
import Data.List ( genericLength )
import Data.List.NonEmpty ( NonEmpty( (:|) ) )
import qualified Data.List.NonEmpty as NEL
import qualified Data.Text as T
import qualified Data.Traversable as DT
import Text.Parsec.Text ( Parser )
import Text.Parsec ( char, try, option, string, noneOf, newline, sepBy1
                   , between, many1, digit )
import Text.Parsec.Prim ( parse )

import LTS ( LTS(..) )
import qualified MTBDD
import NFA ( BoundarySignal(..), BoundarySignals, NFA(..)
           , NFAWithBoundaries(..), signalsMapToBDD )

textToNFAWith :: (NFADef String -> Either String r) -> [T.Text] -> r
textToNFAWith f = dieOr . toNFAWithF . toT
  where
    dieOr = either error id

    toNFAWithF = doParse >=> f
    doParse = conv . parse parseNetDef ""
    conv = either (Left . show) Right

    toT = T.unlines

textToNFAWB :: [T.Text] -> NFAWithBoundaries Int
textToNFAWB = textToNFAWith (toNFAWBDef >=> defToNFAWithBoundaries)

textToNFA :: [T.Text] -> NFA Int Int
textToNFA = textToNFAWith ((defToNFA <$>) . toNFADef)

defToNFA :: NFADef [ZOS] -> NFA Int Int
defToNFA (NFADef is ts fs) =
    let listsToVarMap = M.fromListWith (M.unionWith S.union)
        lts = LTS . M.map toBDDs . listsToVarMap $ trans
    in NFA lts (`inNEL` is) (`elem` fs)
  where
    toBDDs = MTBDD.or . map doUnit . M.toList
    doUnit = uncurry (MTBDD.unitWithVars S.empty)

    trans = NEL.toList ts >>= toTrans

    -- ss, ls and ts are all (non-empty) lists, so we use the list Monad to
    -- construct a single list of pairs from source states to a BDD map.
    toTrans (NFATransDef srcs ls trgs) = do
        s <- NEL.toList srcs
        l <- NEL.toList ls
        let converted = convertLabel l
        return (s, M.singleton converted (S.fromList . NEL.toList $ trgs))

    convertLabel = toVarList
      where
        toVarList = foldr go [] . zip [0..]

        -- Ignore stars, their variable's value doesn't matter
        go (pos, x) l = let s = case x of
                                    Zero -> Just False
                                    One -> Just True
                                    Star -> Nothing
                        in maybe l (\s' -> (pos, s') : l) s

defToNFAWithBoundaries :: NFADef NFAWBLabel
                       -> Either String (NFAWithBoundaries Int)
defToNFAWithBoundaries (NFADef is ts fs) = do
    let lSizes@(l, r) = getFirstBoundarySizes ts
    -- Turn the list of transitions into a list of Eithers which are sequenced
    trans <- DT.sequence . runEitherT $ makeTrans lSizes
    let listsToSignalMap = M.fromListWith (M.unionWith S.union)
        lts = LTS . M.map signalsMapToBDD . listsToSignalMap $ trans
        nfa = NFA lts (`inNEL` is) (`elem` fs)
    return $ NFAWithBoundaries nfa l r
  where
    getFirstBoundarySizes (NFATransDef _ (NFAWBLabel l r :| _) _ :| _) =
        (genericLength l, genericLength r)

    makeTrans lSizes = lift (NEL.toList ts) >>= toTrans lSizes

    -- ss, ls and ts are all (non-empty) lists, so we use the list Monad to
    -- construct a single list of pairs from source states to a BDD map.
    toTrans lSizes (NFATransDef srcs ls trgs) = do
        s <- lift $ NEL.toList srcs
        l <- lift $ NEL.toList ls
        converted <- hoistEither $ convertLabel lSizes l
        return (s, M.singleton converted (S.fromList . NEL.toList $ trgs))

    convertLabel :: (Int, Int) -> NFAWBLabel
                 -> Either String (BoundarySignals, BoundarySignals)
    convertLabel (lSize, rSize) (NFAWBLabel ls rs) = do
        check lSize ls True
        check rSize rs False
        Right (toBS ls, toBS rs)
      where
        -- Catch invalid labels
        check size list isLeft = when (genericLength list /= size) $
            Left $ "Invalid length "
                   ++ (if isLeft then "left" else "right")
                   ++ "list: " ++ show list

        -- toBS constructs a BoundarySignals, a Map from Int to (No)Signal
        toBS = foldr go M.empty . zip [0..]

        -- Ignore stars, their variable's value doesn't matter
        go (pos, x) m = let s = case x of
                                    Zero -> Just NoSignal
                                    One -> Just Signal
                                    Star -> Nothing
                        in maybe m (\s' -> M.insert pos s' m) s

inNEL :: (Eq a) => a -> NonEmpty a -> Bool
inNEL x nel = x `elem` NEL.toList nel

-- Turns an NFADef with String labels into a NFADef with NFAWBLabel labels, if
-- its possible to do so.
toNFAWBDef :: NFADef String -> Either String (NFADef NFAWBLabel)
toNFAWBDef = modifyNFADef transformLabel
  where
    transformLabel lbl = case break (== '/') lbl of
        (l, '/' : r) -> toLabel l r
        _ -> Left $ "invalid NFAWB label: " ++ show lbl

    toLabel l r = NFAWBLabel <$> mapM convert l <*> mapM convert r

    convert '0' = Right Zero
    convert '1' = Right One
    convert '*' = Right Star
    convert c = Left $ "Unknown NFA label part: " ++ show c

toNFADef :: NFADef String -> Either String (NFADef [ZOS])
toNFADef = modifyNFADef (mapM convert)
  where
    convert '0' = Right Zero
    convert '1' = Right One
    convert '*' = Right Star
    convert c = Left $ "Unknown NFA label part: " ++ show c

data NFAWBLabel = NFAWBLabel [ZOS] [ZOS]
                deriving Show
data ZOS = Zero
         | One
         | Star
         deriving (Eq, Ord, Show)

-- Transform NFADefs over String labels into arbitrary other labels, using the
-- provided function.
modifyNFADef :: (String -> Either String a) -> NFADef String
             -> Either String (NFADef a)
modifyNFADef f (NFADef is ts fs) =
    (\ts' -> NFADef is ts' fs) <$> DT.mapM transform ts
  where
    transform (NFATransDef src lbls tgt) =
        (\lbls' -> NFATransDef src lbls' tgt) <$> DT.mapM f lbls

data NFADef trans = NFADef
                        (NonEmpty Int)                 -- ^ Initial states
                        (NonEmpty (NFATransDef trans)) -- ^ Transitions
                        [Int]                          -- ^ Final states
                  deriving Show

data NFATransDef l = NFATransDef
                        (NonEmpty Int) -- ^ Source states
                        (NonEmpty l)   -- ^ Labels
                        (NonEmpty Int) -- ^ Target states
                   deriving Show

-- Parse a Net definition:
--  NET ::= PLACES, "\n", TRANS, { TRANS }, "\n", MBPLACES "\n";
--
--  PLACE ::= {- Natural Number -};
--
--  MBPLACES ::= []
--            |  PLACES;
--
--  PLACES ::= PLACE
--          |  PLACE, ",", PLACES;
--
--  TRANS ::= PLACES, "--", LABELS, "->", PLACES;
--
--  LABELS ::= LABEL
--          | LABEL, ",", LABELS;
--
--  LABEL ::= {- Anything but ',' or '-' -}
--
--
-- E.g.:
--     0
--     0--a,b,c->1
--     0--a->0
--     1
--
-- is the NFA that has two states and accepts any string a*(a|b|c).
parseNetDef :: Parser (NFADef String)
parseNetDef =
    NFADef <$> (parsePlaces <* newline)
           <*> (NEL.fromList <$> many1 (try (parseNFATrans <* newline)))
           <*> option [] (NEL.toList <$> parsePlaces <* option '\n' newline)
  where
    commaSep1 x = sepBy1 x (char ',')

    parseInt = read <$> many1 digit

    parsePlaces = NEL.fromList <$> commaSep1 parseInt

    parseNFATrans =
        NFATransDef <$> parsePlaces
                    <*> between (string "--") (string "->") parseLabels
                    <*> parsePlaces

    parseLabels = NEL.fromList <$> (commaSep1 . many1 $ noneOf "-,")

