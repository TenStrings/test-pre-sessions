{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-pattern-inline" @-}
{-@ LIQUID "--no-adt" @-}
{-@ LIQUID "--exact-data-cons" @-}

{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-pattern-inline" @-}

module Main where

import Lib
import Control.Concurrent.MVar
import RIO
import qualified Data.Set as Set
import Data.Map
import Data.Map(Map)

main :: IO ()
main = mainFunc
