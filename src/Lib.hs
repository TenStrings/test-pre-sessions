{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-pattern-inline" @-}
{-@ LIQUID "--no-adt" @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--diffcheck" @-}

{-# LANGUAGE TypeFamilyDependencies  #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FunctionalDependencies #-}

module Lib where
import Control.Concurrent (Chan, MVar, forkIO, newEmptyMVar, putMVar, takeMVar)
import Prelude
import Data.Bifunctor (Bifunctor(bimap))
import Data.Functor ((<$>))
import Control.Applicative ((<|>))
import Data.Tuple (swap)
import Control.Monad (void)
import RIO (RIO (RIO), rState, World (W), liftRIO)
import qualified Data.Set as Set
import qualified Data.Set as Map
import Data.Map (Map)
import Unsafe.Coerce (unsafeCoerce)

mainFunc = do
    putStrLn "running session examples"
    sumSesh

-- variables de estado

{-@ measure lastVal :: World -> Int @-}

{-@ predicate EmptyWorld W = lastVal W = 0 @-}

{-@ predicate NextWorld W1 V W2 = LastValT W1 V W2 @-}

-- helper
{-@ predicate Pure W1 W2 = W1 = W2 @-}


data Asc
data Sum
data Any

{-@ assume doA :: Session s => v1:Int -> Send s -> RIO<{\w -> lastVal w < v1}, {\w1 b w2 -> lastVal w2 = v1}> s @-}
doA :: Session s => Int -> Send s -> RIO s
doA = undefined

-- ex 2
--
newtype SumCnt
  = MkSumCnt (Select (Send SumCnt) (Recv End))

{-@ sumCnt :: SumCnt -> RIO <{\w -> EmptyWorld w}> () @-}
sumCnt :: SumCnt -> RIO ()
sumCnt (MkSumCnt s) = do 
    s <- selectLeft s
    MkSumCnt s <- sendAsc 100 s
    s <- selectLeft s
    MkSumCnt s <- sendAsc 200 s
    s <- selectLeft s
    MkSumCnt s <- sendAsc 300 s
    s <- selectLeft s
    MkSumCnt s <- sendAsc 400 s
    s <- selectLeft s
    MkSumCnt s <- sendAsc 500 s
    s <- selectLeft s
    MkSumCnt s <- sendAsc 600 s
    s <- selectRight s
    (tot, s) <- recv s

    liftRIO $ print tot
    close s


instance Session SumCnt
  where
    newS = undefined 

s = undefined

sumSesh = fmap fst $ rState (newS >>= sumCnt) $ W


-- * Session types
--
data C a

{-@ data Send s = Send s @-}
data Send s = Send s

{-@ data Recv a s = Recv (C (a, s)) @-}
data Recv a s = Recv (C (a, s))
data End      = End ()

--
{-@ data variance Recv covariant covariant @-}
{-@ data variance Send contravariant covariant @-}


-- * Duality and session initiation

class Session s where
  newS :: RIO s

instance Session s => Session (Send s) where
  newS = undefined

instance Session s => Session (Recv s) where
  newS = undefined

instance Session End where
  newS = undefined

instance Session () where
  newS = undefined


-- * Communication primitives

{-@ assume recv :: Recv Int s -> RIO<{\w -> true}, {\w1 v w2 -> NextWorld w1 (fst v) w2}> (Int, s) @-}
recv :: Recv Int s -> RIO (Int, s)
recv = undefined

{-@ close :: End -> RIO <{\x -> true}, {\w1 b w2 -> Pure w1 w2}> () @-}
close :: End -> RIO ()
close (End s) = undefined

--
-- branching

type Select s_1 s_2 = Send (Either (s_1) (s_2)) ()

{-@ assume selectLeft :: Session s => Select s_1 s_2 -> RIO<{\w1 -> true}, {\w1 v w2 -> Pure w1 w2 }> s_1 @-}
selectLeft :: (Session s_1) => Select s_1 s_2 -> RIO s_1
selectLeft (Send s) = undefined 

{-@ assume selectRight :: Session s => Select s_1 s_2 -> RIO<{\w1 -> true}, {\w1 v w2 -> Pure w1 w2}> s_2 @-}
selectRight :: (Session s_2) => Select s_1 s_2 -> RIO s_2
selectRight (Send s) = undefined 

-- * One-shot channels

