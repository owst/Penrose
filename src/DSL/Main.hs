module DSL.Main where

import Prelude hiding (any)
import Control.Monad.Error ()
import Control.Monad.State (StateT, runStateT)

import DSL.Basics
import DSL.Group
import DSL.Context
import DSL.Unify
import DSL.Inference


main :: IO ()
main = putStrLn "hi"
