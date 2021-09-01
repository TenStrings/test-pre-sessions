{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}

{-# LANGUAGE TypeFamilyDependencies  #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE UndecidableInstances #-}

module Lib where
import Control.Concurrent (Chan, MVar, forkIO, newEmptyMVar, putMVar, takeMVar)
import Prelude
import Data.Bifunctor (Bifunctor(bimap))
import Data.Functor ((<$>))
import Data.Tuple (swap)
import Control.Monad (void)

mainFunc = do
    example0
    putStrLn "hello world"

client0 s = do
    s <- send' 5 s
    (y, s) <- recv' s
    close' s
    putStrLn "end client"

{-@ type Odd = {i: Int | i mod 2 = 0 }@-}
{-@ type Even = {i: Int | i mod 2 = 1 }@-}

{-@ server0 :: (Recv Odd (Send Even End)) -> IO () @-}
server0 :: (Recv Int (Send Int End)) -> IO ()
server0 s = do
    (x, s) <- recv' s
    s <- send' (x + 1) s 
    close' s
    -- putStrLn "end server"

example0 = connect' client0 server0

-- * Session types

data Send a s = Send (SendOnce (a, Dual s))
data Recv a s = Recv (RecvOnce (a, s))
data End      = End SyncOnce

{-@ data variance Recv covariant covariant @-}
{-@ data variance Send contravariant covariant @-}

-- * Duality and session initiation

-- con esto ghc da stack overflow, o sea, Session (Dual s)
-- class ( Session (Dual s), Dual (Dual s) ~ s) => Session s where
class (Dual (Dual s) ~ s) => Session s where
  type Dual s = result | result -> s
  newS :: IO (s, Dual s)

instance Session s => Session (Send a s) where
  type Dual (Send a s) = Recv a (Dual s)
  newS = bimap Send Recv <$> onew

instance Session s => Session (Recv a s) where
  type Dual (Recv a s) = Send a (Dual s)
  newS = bimap Recv Send . swap <$> onew

instance Session End where
  type Dual End = End
  newS = bimap End End <$> onewSync

instance Session () where
  type Dual () = ()
  newS = return ((), ())


-- * Communication primitives

{-@ send' :: Session s => v1:a -> Send {v2:a | v1 = v2 } s -> IO s @-}
send' :: Session s => a -> Send a s -> IO s
send' x (Send ch_s) = do
  (here, there) <- newS
  osend ch_s (x, there)
  return here

recv' :: Recv a s -> IO (a, s)
recv' (Recv ch_r) = orecv ch_r

close' :: End -> IO ()
close' (End sync) = osync sync

connect' :: (Session s) => (s -> IO ()) -> (Dual s -> IO a) -> IO a
connect' k1 k2 = do (s1, s2) <- newS; void (forkIO (k1 s1)); k2 s2

-- * One-shot channels

data SendOnce a = SendOnce (MVar a)
data RecvOnce a = RecvOnce (MVar a)

{-@ data variance SendOnce covariant @-}
{-@ data variance RecvOnce covariant @-}

onew :: IO (SendOnce a, RecvOnce a)
onew = bimap SendOnce RecvOnce <$> dup2 newEmptyMVar
    where 
        -- In the linear version, this comes from somewhere else
        dup2 :: IO (MVar a) -> IO (MVar a, MVar a)
        dup2 first = do
            f <- first 
            return (f, f)

osend :: SendOnce a -> a -> IO ()
osend (SendOnce mvar) = putMVar mvar

orecv :: RecvOnce a -> IO a
orecv (RecvOnce mvar) = takeMVar mvar

-- * Synchronisation construct

data SyncOnce = SyncOnce (SendOnce ()) (RecvOnce ())

onewSync :: IO (SyncOnce, SyncOnce)
onewSync = do
  (ch_s1, ch_r1) <- onew
  (ch_s2, ch_r2) <- onew
  return (SyncOnce ch_s1 ch_r2, SyncOnce ch_s2 ch_r1)

osync :: SyncOnce -> IO ()
osync (SyncOnce ch_s ch_r) = do osend ch_s (); orecv ch_r