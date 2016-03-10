{-# LANGUAGE OverloadedStrings, LambdaCase, TupleSections, CPP #-}
module DSL.ComponentsAndWiringParser
    ( parseComponentsAndWiring
    , ComponentsAndWiring(..)
    , WiringDefinition(..)
    , PlaceDef(..)
    , NetDefinition(..)
    , PortOrNamedBoundary(..)
    , InOutTest(..)
    , parseNetDefinition
    ) where

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative ( Alternative, (<|>), (<$>), (<*>), (*>), (<*), many, pure )
#else
import Control.Applicative ( (<|>), many )
#endif

import Control.Monad.Identity ( Identity )
import qualified Data.Text as T

import Text.Parsec ( char, parse, try, option )
import Text.Parsec.Text ( Parser )
import Text.Parsec.Token ( GenTokenParser, GenLanguageDef(..) )
import Text.Parsec.Prim ( getInput, parserFail, parserReturn )
import Text.ParserCombinators.Parsec.Char ( alphaNum, string )
import qualified Text.ParserCombinators.Parsec.Token as Tok

import Prelude hiding ( lex )

import DSL.Expr ( RawExpr )
import DSL.RawExprParser ( parseRawExpr )

import Marking ( TokenStatus(..), WildCardMarks(..) )

data ComponentsAndWiring = ComponentsAndWiring [NetDefinition] WiringDefinition
                             deriving Show

data WiringDefinition = WiringDefinition [String] RawExpr
                      deriving Show

data PlaceDef = PlaceDef
                    String        -- Name
                    TokenStatus   -- Init Marking
                    WildCardMarks -- Wanted Marking
              deriving Show

data NetDefinition = NetDefinition
                        Bool                   -- Use interleaving semantics?
                        String                 -- Name
                        [PlaceDef]             -- Places
                        [String]               -- Left boundaries
                        [String]               -- Right boundaries
                        [TransitionDefinition] -- Transitions
                   deriving Show

data InOutTest = In
               | Out
               | Test
               deriving Show

data PortOrNamedBoundary = Port String InOutTest
                         | NamedBoundary String
                         deriving Show

type TransitionDefinition = [PortOrNamedBoundary]

languageDef :: GenLanguageDef T.Text u Identity
languageDef = LanguageDef
    { Tok.commentStart   = ""
    , Tok.commentEnd     = ""
    , Tok.commentLine    = "--"
    , Tok.nestedComments = False
    , Tok.identStart     = alphaNum
    , Tok.identLetter    = alphaNum
    , Tok.opStart        = char '!'
    , Tok.opLetter       = char '!'
    , Tok.reservedOpNames= []
    , Tok.reservedNames = [ "NET"
                          , "PLACES"
                          , "LBOUNDS"
                          , "RBOUNDS"
                          , "TRANS"
                          , "WIRING"
                          ]
    , Tok.caseSensitive  = True
    }

lexer :: GenTokenParser T.Text () Identity
lexer = Tok.makeTokenParser languageDef

identifier :: Parser String
identifier = Tok.identifier lexer

braceWrapped :: Parser r -> Parser r
braceWrapped = Tok.braces lexer

reserved :: String -> Parser ()
reserved = Tok.reserved lexer

lex :: Parser r -> Parser r
lex = Tok.lexeme lexer

-- Used to import pre-defined library nets
parseNetDefinition :: T.Text -> Either String NetDefinition
parseNetDefinition = parseWithErr parseNetDef

parseWithErr :: Parser p -> T.Text -> Either String p
parseWithErr p = either (Left . show) Right . parse p ""

parseComponentsAndWiring :: T.Text -> Either String ComponentsAndWiring
parseComponentsAndWiring = parseWithErr parseComponentsAndWiring'
  where
    parseComponentsAndWiring' = ComponentsAndWiring
                                <$> (Tok.whiteSpace lexer *> many parseNetDef)
                                <*> namedSection "WIRING" parseWiringDef

namedSection :: String -> Parser r -> Parser r
namedSection n p = reserved n *> p

parseNetDef :: Parser NetDefinition
parseNetDef =
    NetDefinition <$> namedSection "NET" parseInterleaved
                  <*> identifier
                  <*> namedSection "PLACES" parsePlaces
                  <*> namedSection "LBOUNDS" parseBoundaryNames
                  <*> namedSection "RBOUNDS" parseBoundaryNames
                  <*> namedSection "TRANS" parseTrans
  where
    comma = Tok.comma lexer
    angleWrapped = Tok.angles lexer
    bracketWrapped = Tok.brackets lexer

    parseInterleaved = option False (reserved "INTERLEAVED" *> pure True)

    parsePlaces = bracketWrapped $ commaSep parsePlace

    parsePlace = angleWrapped $
        PlaceDef <$> (identifier <* comma)
                 <*> (parseTokStatus <* comma)
                 <*> parseWildCardMark

    parseTokStatus =   tagged '0' Absent
                   <|> tagged '1' Present

    parseWildCardMark =   tagged '0' No
                      <|> tagged '1' Yes
                      <|> tagged '*' DontCare

    parseBoundaryNames = bracketWrapped $ commaSep identifier

    parseTrans = braceWrapped $ commaSep parseTransition

    parseTransition = braceWrapped $ commaSep parsePort

    outOrTest =     tagged '>' Out
                <|> tagged '?' Test

    parsePort =     flip Port <$> tagged '>' In <*> identifier
                <|> try (Port <$> identifier <*> outOrTest)
                <|> NamedBoundary <$> identifier

commaSep :: Parser a -> Parser [a]
commaSep = Tok.commaSep lexer

parseWiringDef :: Parser WiringDefinition
parseWiringDef = WiringDefinition <$> option [] parseImport
                                  <*> parseExpr
  where
    -- Integrate our Happy parser to parse the expression
    parseExpr = do
        input <- getInput
        case parseRawExpr input of
            Left err -> parserFail err
            Right rawExpr -> parserReturn rawExpr

    parseImport = lex (string "IMPORT") *> commaSep identifier

-- |@tagged c res@ uses the character @c@ to disambiguate a parse of res.
tagged :: Char -> r -> Parser r
tagged c res = lex (char c) *> pure res
