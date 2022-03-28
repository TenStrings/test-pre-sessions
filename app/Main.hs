--{-@ LIQUID "--prune-unsorted" @-}
--{-@ LIQUID "--ple" @-}
--{-@ LIQUID "--reflection" @-}
--{-@ LIQUID "--no-pattern-inline" @-}
--{-@ LIQUID "--no-adt" @-}
--{-@ LIQUID "--exact-data-cons" @-}
--
--{-@ LIQUID "--short-names" @-}
--{-@ LIQUID "--no-pattern-inline" @-}

module Main where

import Lib

main :: IO ()
main = mainFunc
