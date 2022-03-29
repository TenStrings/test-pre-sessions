{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-@ LIQUID "--prune-unsorted"        @-}

module Lib where

import qualified Control.Concurrent.Chan       as C
import           Control.Effect.Sessions
import           Data.Type.Set           hiding ( (:->) )
import           GHC.Exts                       ( Constraint
                                                , IsString
                                                )
import           GHC.TypeLits
import           Unsafe.Coerce
import           Prelude                 hiding ( Monad(..)
                                                , fail
                                                , print
                                                , putStrLn
                                                )
import qualified Prelude                       as P

mainFunc = run $ do
  -- divProc >>
  -- simpleDelg >>
  -- repProc >>
  gtProc


data NonZero = NZ Int deriving (Show)

{-@ NZ :: {i:Int | i > 0 } -> NonZero @-}

divServer (c :: Chan (Ch "c")) (d :: (Chan (Ch "d"))) = do
  x      <- recv c
  (NZ y) <- recv c
  send d (x `div` y)

divClient (c :: Chan (Op "c")) (d :: (Chan (Op "d"))) = do
  send c (2 :: Int)
  send c (NZ 1) -- unsound
  answer <- recv d
  putStrLn $ "result " ++ show answer

divProc =
  new $ \(c, c') -> new $ \(d, d') -> divServer c d `par` divClient c' d'

-- Delegation

-- serverD :: _ -> _
serverD (c :: (Chan (Ch "c"))) = do
  chRecvSeq c (\(d :: Chan (Ch "x")) -> send d (NZ 0))

clientD (c :: Chan (Op "c")) = new
  (\(d :: (Chan (Ch "d")), d') -> do
    chSend c d
    (NZ y) <- recv d'
    putStrLn $ show y
  )

simpleDelg = new $ \(c, c') -> serverD c `par` clientD c'

-- Recursive

repInp c p = affineFix
  (\f -> \() -> do
    (x :: Int) <- recv c
    print $ "received: " ++ show x
    case x of
      0 -> subL $ subEnd c $ return ()
      n -> subR $ do
        k <- chRecv c
        (k p) `par` (f ())
  )
  ()

serverA (c :: (Chan (Ch "c"))) = repInp
  c
  (\(d :: (Chan (Ch "d"))) -> do
    (NZ x) <- recv d
    print x
  )

clientA (c :: (Chan (Op "c"))) = new
  (\(d :: Chan (Ch "d"), d') -> do
    send c (1 :: Int)
    rsend c d
    send d' (NZ 0)
    send c  (0 :: Int)
  )

repProc = new $ \(c, c') -> do
  (serverA c) `par` (clientA c')

-- Exp
{- 
  try to check that two different values sent/received are different
-}

-- this won't parse, so it is not possible to add refinements this way inside
-- the list/maps 
-- TODO: check if it is possible to reflect on some type-level functions in any
-- case, though, it should fail anyway without any refinements, as it should be
-- obvious that x == y so we get NZ 0
-- 
-- {-@ gtServer
--   :: Chan ('Ch _)
--      -> Chan ('Ch _)
--      -> Process
--           '[ 'Ch _ 'Control.Effect.Sessions.:-> (Int ':? (Int ':? 'End)),
--              'Ch _ 'Control.Effect.Sessions.:-> (NonZero ':! 'End)]
--           ()
-- @-}
gtServer
  :: Chan ('Ch "c")
     -> Chan ('Ch "d")
     -> Process
          '[ 'Ch "c" 'Control.Effect.Sessions.:-> (Int ':? (Int ':? 'End)),
             'Ch "d" 'Control.Effect.Sessions.:-> (NonZero ':! 'End)]
          ()
gtServer (c :: Chan (Ch "c")) (d :: (Chan (Ch "d"))) = do
  x <- recv c
  y <- recv c
  send d $ NZ (x - y)

gtClient
  :: (Num t1, Num t2, Show a) =>
     Chan ('Op "c")
     -> Chan ('Op "d")
     -> Process
          '[ 'Op "c" 'Control.Effect.Sessions.:-> (t1 ':! (t2 ':! 'End)),
             'Op "d" 'Control.Effect.Sessions.:-> (a ':? 'End)]
          ()
gtClient (c :: Chan (Op "c")) (d :: (Chan (Op "d"))) = do
  send c $ 1
  send c $ 1
  answer <- recv d
  putStrLn $ "result " ++ show answer

gtProc = new $ \(c, c') -> new $ \(d, d') -> gtServer c d `par` gtClient c' d'
