-- {-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-pattern-inline" @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--no-adt" @-}

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
import RIO (RIO (RIO), rState, World (cnt, vs, W), emptyWorld, t1, liftRIO, setV, vmap, vdom, getEntry, rioAssert, getEntry2)
import qualified Data.Set as Set
import qualified Data.Set as Map
import Data.Map (Map)
{-@ embed  Map as Map_t @-}

mainFunc = do
--    top
--    top2
    incrS
-- 
{-@ client :: (Send Int (Recv Int End)) -> RIO <{\w -> EmptyWorld w}> () @-}
client :: (Send Int (Recv Int End)) -> RIO ()
client s = do
    s <- send 5 s
    expect 6
    (y, s) <- recv s

    -- esto anda
    x <- getEntry 1
    rioAssert $ y == x + 1
    rioAssert $ y == 6

    -- pero esto solo anda con precondiciones bastante fuertes supongo que
    -- porque al extraer la función la inferencia  cambia
    -- c <- server_c1
    -- rioAssert c

    -- c2 <- server_c2
    -- liftRIO $ print c2
    -- rioAssert c2

    close s

{-@ server_c1 :: RIO<{\w -> Set_mem 1 (listElts(vdom (vs w))) && Set_mem 2 (listElts(vdom (vs w))) }, 
      {\w1 x w2 -> Pure w1 w2 && 
      x <=> Map_select (vmap (vs w1)) 2 = (Map_select (vmap (vs w1)) 1) + 1}>
      Bool @-}
server_c1 :: RIO Bool 
server_c1 = do
  x <- getEntry 1
  y <- getEntry 2
  return $ y == x + 1 


{-@ server :: (Recv Int (Send Int End)) -> RIO <{\w -> EmptyWorld w}> () @-}
server :: (Recv Int (Send Int End)) -> RIO ()
server s = do
    expect anyInt
    (x, s) <- recv s
    s <- send (x + 1) s 

    y <- getEntry 2
    rioAssert $ y == x + 1

    close s

{-@ assume anyInt :: Int @-}
anyInt :: Int
anyInt = undefined

incrS = connect client server

-- * Session types

data Send a s = Send (SendOnce (a, Dual s))
{-@ data Recv a s = Recv (RecvOnce (a, s)) @-}
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
  newS = bimap Send Recv <$> new'

instance Session s => Session (Recv a s) where
  type Dual (Recv a s) = Send a (Dual s)
  newS = bimap Recv Send . swap <$> new'

instance Session End where
  type Dual End = End
  newS = bimap End End <$> newSync

instance Session () where
  type Dual () = ()
  newS = return ((), ())


-- * Communication primitives

{-@ send :: Session s => v1:Int -> Send {v2:Int | v1 = v2 } s -> RIO<{\w1 -> IsPrev w1}, {\w1 b w2 -> UpdateDomain w2 w1 && AddValueIndex w2 v1 w1 }> s @-}
send :: Session s => Int -> Send Int s -> RIO s
send x (Send ch_s) = do
  setV x -- add value to the environment
  (here, there) <- (liftRIO newS)
  liftRIO $ send' ch_s (x, there)
  return here

{-@ expect :: g:Int -> RIO <{\w1 -> IsPrev w1}, {\w1 b w2 -> UpdateDomain w2 w1 && AddValueIndex w2 g w1 }> () @-}
expect :: Int -> RIO ()
expect v = do 
  setV v
  return ()

{-@ assume recv :: Recv Int s -> RIO <{\w1 -> cnt w1 >= 1}, {\w1 b w2 -> w1 = w2 && (fst b) = Map_select (vmap (vs w1)) (cnt w1) }> (Int, s) @-}
recv :: Recv Int s -> RIO (Int, s)
recv (Recv ch_r) = do
  liftRIO $ recv' ch_r

{-@ close :: End -> RIO <{\x -> true}, {\w1 b w2 -> w1 = w2}> () @-}
close :: End -> RIO ()
close (End s) = liftRIO $ sync s

-- TODO: sacar este ignore
{-@ ignore connect @-}
{-@ connect :: (Session s) => (s -> RIO <{\w -> EmptyWorld w}> ()) -> (Dual s -> RIO <{\w -> EmptyWorld w}> a) -> IO a @-}
connect :: (Session s) => (s -> RIO ()) -> (Dual s -> RIO a) -> IO a
connect k1 k2 = do 
  (s1, s2) <- newS
  void (forkIO (gi (k1 s1)))
  gi (k2 s2)
  where gi rio = let io = rState rio $ emptyWorld in fmap fst io

-- * One-shot channels

data SendOnce a = SendOnce (MVar a)
data RecvOnce a = RecvOnce (MVar a)

{-@ data SendOnce a = SendOnce (MVar a) @-}
{-@ data RecvOnce a = RecvOnce (MVar a) @-}

{-@ data variance SendOnce covariant @-}
{-@ data variance RecvOnce covariant @-}

new' :: IO (SendOnce a, RecvOnce a)
new' = bimap SendOnce RecvOnce <$> dup2 newEmptyMVar
    where 
        -- In the linear version, this comes from somewhere else
        dup2 :: IO (MVar a) -> IO (MVar a, MVar a)
        dup2 first = do
            f <- first 
            return (f, f)

send' :: SendOnce a -> a -> IO ()
send' (SendOnce mvar) = putMVar mvar

recv' :: RecvOnce a -> IO a
recv' (RecvOnce mvar) = takeMVar mvar

-- * Synchronisation construct

data SyncOnce = SyncOnce (SendOnce ()) (RecvOnce ())

{-@ ignore newSync @-}
newSync :: IO (SyncOnce, SyncOnce)
newSync = do
  (ch_s1, ch_r1) <- new'
  (ch_s2, ch_r2) <- new'
  return (SyncOnce ch_s1 ch_r2, SyncOnce ch_s2 ch_r1)

sync :: SyncOnce -> IO ()
sync (SyncOnce ch_s ch_r) = do send' ch_s (); recv' ch_r

--- tests

-- top = do 
--   (_, w) <- (rState testing) emptyWorld
--   print $ vs w

top2 = do
  print t1
  return ()

--






--
