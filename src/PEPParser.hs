{-# LANGUAGE TemplateHaskell, OverloadedStrings, FlexibleContexts, CPP #-}
module PEPParser where

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative ( Alternative, (<|>), (<$>), (<*>), (*>), (<*), many, pure )
#else
import Control.Applicative ( (<|>), many )
#endif

import Control.Lens ( makeLenses )
import Control.Monad ( void, (>=>) )
import Data.Number.Nat ( Nat, toNat )
import qualified Data.ByteString as BIO
import Data.Text ( Text, pack, unpack )
import qualified Data.Text as T
import Data.Text.Read ( decimal, signed )
import Data.Text.Encoding ( decodeLatin1 )
import qualified Data.Text.IO as TIO
import Text.Parsec.Prim ( parse, try, parserFail, parserReturn, skipMany )
import Text.Parsec.Text ( Parser )
import Text.Parsec.Char ( char, string, newline, digit, anyChar, noneOf )
import Text.Parsec.Combinator ( sepBy, option, many1, manyTill )

-- From: http://parsys.informatik.uni-oldenburg.de/~pep/Paper/formats_all.ps.gz

data LLNetType = PTNet
               | PetriBox
               deriving (Eq, Show)

data FormatType = N
                | N2
                deriving (Eq)

instance Show FormatType where
    show N = "FORMAT_N"
    show N2 = "FORMAT_N2"

data Header = Header LLNetType FormatType
            deriving (Eq, Show)

newtype Thickness = Thickness Nat
                  deriving (Eq, Show)

newtype Size = Size Nat
             deriving (Eq, Show)

data Default = DefaultBlock [BlockDefault]
             | DefaultPlace [PlaceDefault]
             | DefaultTransition [TransitionDefault]
             | DefaultArc [ArcDefault]
             deriving (Eq, Show)

data BlockDefault = BlockSize Size
                  | BlockThickness Thickness
                  deriving (Eq, Show)

data PlaceDefault = PlaceDefaultableAttribute DefaultableExtraAttribute
                  | PlaceSize Size
                  | PlaceThickness Thickness
                  deriving (Eq, Show)

data TransitionDefault = TransitionDefaultableAttribute
                            DefaultableExtraAttribute
                       | TransitionSize Size
                       | TransitionThickness Thickness
                       deriving (Eq, Show)

data ArcDefault = ArcDefaultableAttribute DefaultableArcAttribute
                | ArcThickness Thickness
                deriving (Eq, Show)

data DefaultableArcAttribute = Weight Int
                             | WeightRelativePos Position
                             deriving (Eq, Show)

data DefaultableExtraAttribute = NameRelativePos Position
                               | Meaning Text
                               deriving (Eq, Show)

newtype Position = Position (Int, Int)
                 deriving (Eq, Show)

data InfinityOrNum = Infinity
                   | Number Nat
                   deriving (Eq, Show)

data ObjectData = ObjectData
    { _objIDName :: Maybe (Either (Int, Text) Text)
    , _objectPos :: !Position
    } deriving (Eq, Show)

$(makeLenses ''ObjectData)

data CommonExtraAttribute = MeaningRelativePos Position
                          | Reference Text
                          | CommonDefaulted DefaultableExtraAttribute
                          deriving (Eq, Show)

data BlockAttribute = BlockCommon CommonExtraAttribute
                    | BlockBlocks [Int]
                    deriving (Eq, Show)

data Block = Block
    { _bData :: ObjectData
    , _bAttributes :: [BlockAttribute]
    } deriving (Eq, Show)

$(makeLenses ''Block)

data PlaceAttribute = PlaceCommon CommonExtraAttribute
                    | PlaceInitialMarking Bool
                    | PlaceCurrentMarking Bool
                    | PlaceCapacity InfinityOrNum
                    | PlaceEntryPlace
                    | PlaceExitPlace
                    | PlaceBlocks [Int]
                    deriving (Eq, Show)

data Place = Place
    { _pData :: !ObjectData
    , _pAttributes :: [PlaceAttribute]
    } deriving (Eq, Show)

$(makeLenses ''Place)

data TransitionAttribute = TransitionCommon CommonExtraAttribute
                         | TransitionBlocks [Int]
                         | TransitionSynchronisationTransition
                         | TransitionPhantomTransitions [Int]
                         | TransitionInvisibleLevel Int
                         deriving (Eq, Show)

data Transition = Transition
    { _tData :: !ObjectData
    , _tAttributes :: [TransitionAttribute]
    } deriving (Eq, Show)

$(makeLenses ''Transition)

data PhantomTransitionAttribute
    = PhantomTransCommon CommonExtraAttribute
    | PhantomTransBlocks [Int]
    | PhantomTransSynchronisationTransitions [Int]
    deriving (Eq, Show)

data PhantomTransition = PhantomTransition
    { _ptData :: !ObjectData
    , _ptAttributes :: [PhantomTransitionAttribute]
    } deriving (Eq, Show)

$(makeLenses ''PhantomTransition)

newtype PlaceID = PlaceID Int
                deriving (Eq, Show)

newtype TransID = TransID Int
                deriving (Eq, Show)

newtype PTransID = PTransID Int
                 deriving (Eq, Show)

data ArcType = PTArc !PlaceID !TransID
             | TPArc !TransID !PlaceID
             | PPTArc !PlaceID !PTransID
             | PTPArc !PTransID !PlaceID
             deriving (Eq, Show)

data Arc = Arc ArcType [ArcAttribute]
         deriving (Eq, Show)

data ArcAttribute = ArcInvisibleLevel Int
                  | ArcAdditionalPoint Position
                  | ArcDefaulted DefaultableArcAttribute
                  deriving (Eq, Show)

data TextLine = TextLine !Position !Text
              deriving (Eq, Show)

data LLNet = LLNet
    { _llnetHeader :: !Header
    , _llnetDefaults :: ![Default]
    , _llnetBlocks :: ![Block]
    , _llnetPlaces :: ![Place]
    , _llnetTrans :: ![Transition]
    , _llnetPTrans :: ![PhantomTransition]
    , _llnetArcs :: ![Arc]
    , _llnetTextLines :: ![TextLine]
    } deriving (Eq, Show)

$(makeLenses ''LLNet)

spaces :: Parser ()
spaces = skipMany (char ' ')

line :: Parser ()
line = spaces <* optionalComment

optionalComment :: Parser ()
optionalComment = void commentOrNewline
  where
    commentOrNewline = (char '%' <* manyTill anyChar newline) <|> newline

lineNoComment :: Parser ()
lineNoComment = spaces <* newline

parseID :: Parser Int
parseID = parseInt

parseInt :: Parser Int
parseInt = do
    sign <- option '+' (char '+' <|> char '-')
    digits <- many1 digit
    stringToIntParser (sign : digits)
  where
    -- Go via Text to use the signed decimal parser
    stringToIntParser = failOrExtract . signed decimal . pack

    failOrExtract (Left err) = parserFail err
    failOrExtract (Right (i, r))
        | T.null r = parserReturn i
        | otherwise = parserFail $
            "Remaining text after parseInt on many1 digit" ++ unpack r

parseBinaryAsBool :: Parser Bool
parseBinaryAsBool =     const False <$> char '0'
                    <|> const True <$> char '1'

parseInfinityOrNum :: Parser InfinityOrNum
parseInfinityOrNum =
        const Infinity <$> (char '-' *> parseInt)
    <|> Number <$> parseNat

parseNat :: Parser Nat
parseNat = toNat <$> parseInt

parseQuotedText :: Parser Text
parseQuotedText = parseQuoted $ pack <$> many (noneOf "\"")

parseQuoted :: Parser a -> Parser a
parseQuoted p = dblQuote *> p <* dblQuote
  where
    dblQuote = char '"'

parseSize :: Parser Size
parseSize = taggedParse 's' (Size <$> parseNat)

parseThickness :: Parser Thickness
parseThickness = taggedParse 't' (Thickness <$> parseNat)

parsePosition :: Parser Position
parsePosition = makePos <$> (parseInt <* char '@') <*> parseInt
  where
    makePos x y = Position (x, y)

parseHeader :: Parser Header
parseHeader = pPepFile *> pHeader
  where
    pPepFile = string "PEP" *> lineNoComment

    pHeader = Header <$> (pType <* lineNoComment)
                     <*> (pFormat <* lineNoComment)

    pType = (const PetriBox <$> try (string "PetriBox")) <|>
            (const PTNet <$> string "PTNet")

    pFormat = (const N2 <$> try (string "FORMAT_N2")) <|>
              (const N <$> string "FORMAT_N")

-- TODO: this!
parseDefaults :: Parser [Default]
parseDefaults = many parseDefault

-- |manyOnLine @c@ @p@ parses 0 or more occurrences of @p@, followed by an EOL,
-- before applying the constructor c to the resulting list.
manyOnLine :: ([a] -> b) -> Parser a -> Parser b
manyOnLine c p = c <$> many p <* lineNoComment

parseDefault :: Parser Default
parseDefault =
    strTaggedParse "DBL" (manyOnLine DefaultBlock parseBlockDefault)
    <|> strTaggedParse "DPL" (manyOnLine DefaultPlace parsePlaceDefault)
    <|> strTaggedParse "DTR" (manyOnLine DefaultTransition parseTransitionDefault)
    <|> strTaggedParse "DPT" (manyOnLine DefaultArc parseArcDefault)

parseBlockDefault :: Parser BlockDefault
parseBlockDefault =
        BlockSize <$> parseSize
    <|> BlockThickness <$> parseThickness

parsePlaceDefault :: Parser PlaceDefault
parsePlaceDefault =
        PlaceDefaultableAttribute <$> parseDefaultableExtraAttribute
    <|> PlaceSize <$> parseSize
    <|> PlaceThickness <$> parseThickness

parseTransitionDefault :: Parser TransitionDefault
parseTransitionDefault =
        TransitionDefaultableAttribute <$> parseDefaultableExtraAttribute
    <|> TransitionSize <$> parseSize
    <|> TransitionThickness <$> parseThickness

parseArcDefault :: Parser ArcDefault
parseArcDefault =
        ArcDefaultableAttribute <$> parseDefaultableArcAttribute
    <|> ArcThickness <$> parseThickness

-- |parseAttribute takes a disambiguation character and a parser, and uses
-- taggedParse, ignoring any trailing spaces.
parseAttribute :: Char -> Parser a -> Parser a
parseAttribute c p = taggedParse c p <* spaces

parseDefaultableArcAttribute :: Parser DefaultableArcAttribute
parseDefaultableArcAttribute =
            parseAttribute 'w' (Weight <$> parseInt)
        <|> parseAttribute 'n' (WeightRelativePos <$> parsePosition)

-- Object Data is an ID, name and position. They must appear in that order if
-- they appear, but ID and name may be left off. If the id doesn't appear, it
-- is assumed to be 1-indexed.
parseObjectData :: Parser ObjectData
parseObjectData = parseRaw >>= toObjData
  where
    parseRaw = (,,) <$>
                  option Nothing (try (Just <$> spaced parseID)) <*>
                  option Nothing (spaced (Just <$> parseQuotedText)) <*>
                  spaced parsePosition

    toObjData (Nothing, Nothing, p) = return $ ObjectData Nothing p
    toObjData (Nothing, Just n, p) = return $ ObjectData (Just (Right n)) p
    toObjData (Just i, Just n, p) = return $ ObjectData (Just (Left (i, n))) p
    toObjData input =
        parserFail $ "Object data doesn't meet requirements: " ++ show input
    spaced p = p <* spaces

-- | Parse a "disambiguation" string, and then use the given parser.
strTaggedParse :: String -> Parser a -> Parser a
strTaggedParse t p = try (strNoLine t) *> p

-- | Parse a single "disambiguation" character, and then use the given parser.
taggedParse :: Char -> Parser a -> Parser a
taggedParse c p = char c *> p

parseListOfIDs :: Parser [Int]
parseListOfIDs = parseQuoted $ withParens (sepBy parseID (char ','))
  where
    withParens p = char '(' *> p <* char ')'

parseDefaultableExtraAttribute :: Parser DefaultableExtraAttribute
parseDefaultableExtraAttribute =
        parseAttribute 'n' (NameRelativePos <$> parsePosition)
    <|> parseAttribute 'b' (Meaning <$> parseQuotedText)

parseCommonExtraAttribute :: Parser CommonExtraAttribute
parseCommonExtraAttribute =
        (CommonDefaulted <$> parseDefaultableExtraAttribute)
    <|> parseAttribute 'a' (MeaningRelativePos <$> parsePosition)
    <|> parseAttribute 'R' (Reference <$> parseQuotedText)

parseBlocks :: Parser [Block]
parseBlocks = option [] (strLine "BL" *> many parseBlock)
  where
    parseBlock =
        Block <$> parseObjectData <*> many parseBlockAttribute <* lineNoComment

    parseBlockAttribute =     BlockCommon <$> parseCommonExtraAttribute
                          <|> BlockBlocks <$> parseAttribute 'u' parseListOfIDs

parsePlaces :: Parser [Place]
parsePlaces = strLine "PL" *> many parsePlace
  where
    parsePlace =
        Place <$> parseObjectData <*> many parsePlaceAttribute <* lineNoComment

    parsePlaceAttribute =
            PlaceCommon <$> parseCommonExtraAttribute
        <|> parseAttribute 'M' (PlaceInitialMarking <$> parseBinaryAsBool)
        <|> parseAttribute 'm' (PlaceCurrentMarking <$> parseBinaryAsBool)
        <|> parseAttribute 'k' (PlaceCapacity <$> parseInfinityOrNum)
        <|> parseAttribute 'e' (return PlaceEntryPlace)
        <|> parseAttribute 'x' (return PlaceExitPlace)
        <|> parseAttribute 'u' (PlaceBlocks <$> parseListOfIDs)

parseTransitions :: Parser [Transition]
parseTransitions = strLine "TR" *> many parseTransition
  where
    parseTransition =
        Transition <$> parseObjectData <*>
            many parseTransitionAttribute <* lineNoComment

    parseTransitionAttribute =
            TransitionCommon <$> parseCommonExtraAttribute
        <|> parseAttribute 'v' (TransitionInvisibleLevel <$> parseInt)
        <|> parseAttribute 'u' (TransitionBlocks <$> parseListOfIDs)
        <|> parseAttribute 'S' (return TransitionSynchronisationTransition)
        <|> parseAttribute 'P' (TransitionPhantomTransitions <$> parseListOfIDs)

parsePhantomTrans :: Parser [PhantomTransition]
parsePhantomTrans = option [] (strLine "PTR" *> many parsePhantomTran)
  where
    parsePhantomTran =
        PhantomTransition <$> parseObjectData <*>
            many parsePhantomTransAttribute <* lineNoComment

    parsePhantomTransAttribute =
            PhantomTransCommon <$> parseCommonExtraAttribute
        <|> parseAttribute 'u' (PhantomTransBlocks <$> parseListOfIDs)
        <|> parseAttribute 'P'
                (PhantomTransSynchronisationTransitions <$> parseListOfIDs)


parseArcs :: Bool -> Parser [Arc]
parseArcs isPhantom = many parseArc
  where
    arcDataToArcType lid isTP rid attrs =
        let arcType = case (isPhantom, isTP) of
                          (False, False) -> PTArc (PlaceID lid) (TransID rid)
                          (False, True) -> TPArc (TransID lid) (PlaceID rid)
                          (True, False) -> PPTArc (PlaceID lid) (PTransID rid)
                          (True, True) -> PTPArc (PTransID lid) (PlaceID rid)
        in Arc arcType attrs

    parseArc = arcDataToArcType <$> parseInt
                                <*> parseIsTP
                                <*> parseInt
                                <*> many parseArcAttribute
                                <* lineNoComment

    parseIsTP =     taggedParse '<' (pure True)
                <|> taggedParse '>' (pure False)

    parseArcAttribute =
            ArcDefaulted <$> parseDefaultableArcAttribute
        <|> parseAttribute 'v' (ArcInvisibleLevel <$> parseInt)
        <|> parseAttribute 'J' (ArcAdditionalPoint <$> parsePosition)

parseText :: Parser [TextLine]
parseText = strLine "TX" *> many parseTextLine
  where
    parseTextLine =
        TextLine <$> parsePosition <*> parseQuotedText <* lineNoComment

llNetParser :: Parser LLNet
llNetParser =
    LLNet <$>
    parseHeader <*>
    parseDefaults <*>
    parseBlocks <*>
    parsePlaces <*>
    parseTransitions <*>
    parsePhantomTrans <*>
    parseAllArcs <*>
    optionalList parseText
  where
    concat4 a b c d = a ++ b ++ c ++ d

    parseAllArcs = concat4 <$> taggedArcs "TP" <*>
                               taggedArcs "PT" <*>
                               optionalList (taggedPhantomArcs "PTP") <*>
                               optionalList (taggedPhantomArcs "PPT")

    taggedArcs s = strLine s *> parseArcs False
    taggedPhantomArcs s = strLine s *> parseArcs True
    optionalList = option []

strLine :: String -> Parser ()
strLine s = string s *> line

strNoLine :: String -> Parser ()
strNoLine s = string s *> spaces

parseLLNet :: Text -> IO LLNet
parseLLNet input = case parse llNetParser "" input of
    Left err -> fail $ "parsing failed: " ++ show err
    Right a -> return a

parseFile :: String -> IO LLNet
parseFile = TIO.readFile >=> parseLLNet

parseLatin1File :: String -> IO LLNet
parseLatin1File = BIO.readFile >=> parseLLNet . decodeLatin1
