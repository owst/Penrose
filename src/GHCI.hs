-- Convenience module to pull in the main dependencies for easy testing in the repl.
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
module GHCI where
import LTS
import Nets
import NFA
import ProcessExpr
import MapSetUtils
import Minimisation
import Marking
import PEPParser
import PEP
import Control.Monad

import qualified Data.Traversable as DT
import Data.List
import Safe
import qualified Data.Text as T
import System.PosixCompat.Files
import System.FilePath

import MTBDD
import MTBDD.Internals hiding ( Leaf )
import Control.Applicative
import Control.Arrow
import qualified Data.Set as S
import qualified Data.IntSet as IS
import qualified Data.HashSet as HS
import qualified Data.Map.Strict as M
import Data.Maybe
import Debug.Trace
import System.Directory
import qualified Data.Text.IO as DTIO

import Run
import ParseNFA
import DSL.ComponentsAndWiringParser
import DSL.ProcessParse
import DSL.RawExprLexer
import DSL.RawExprParser
import DSL.Expr

import Prelude hiding ( mapM, id )

import System.Environment
