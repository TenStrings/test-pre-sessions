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
import RIO (RIO (RIO), rState, World (cnt, vs, W), Value(N), emptyWorld, testing, t1, liftRIO, setV, vmap, addV, vdom)
import qualified Data.Set as Set
import qualified Data.Set as Map
import Data.Map (Map)
{-@ embed  Map as Map_t @-}

mainFunc = do
--    top
--    top2
    incrS
-- 
{-@ client :: (Send Value (Recv Value End)) -> RIO <{\w -> EmptyWorld w}> () @-}
client :: (Send Value (Recv Value End)) -> RIO ()
client s = do
    s <- send (N 5) s
    (y, s) <- recv (N 6) s
    server_c
    close s

-- me gustaría poder retornar RIO Bool y escribir el refinement con código, pero
-- no encuentro forma de hacerlo andar (o sea, en realidad no encuentro la forma
-- de asserterarlo después). Pero supongo que se tiene que poder.
-- o sea, vi cosas parecidas en los ejemplos.
{-@ server_c :: RIO<
      {\x -> 
        cnt x = 2 && 
        listElts(vdom (vs x)) = Set_cup (Set_sng 1) (Set_sng 2) &&
        Map_select (vmap (vs x)) 2 = addV (N 1) (Map_select (vmap (vs x)) 1)
        }, 
      {\w1 x w2 -> w1 = w2}> 
      ()
  @-}
server_c :: RIO ()
server_c = return () 

{-@ server :: (Recv Value (Send Value End)) -> RIO <{\w -> EmptyWorld w}> () @-}
server :: (Recv Value (Send Value End)) -> RIO ()
server s = do
    (N x, s) <- recv (N 5) s
    s <- send (N (x + 1)) s 
    close s


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

-- este assume no debería hacer falta supongo, pero por ahora es más fácil
{-@ assume send :: Session s => v1:Value -> Send {v2:Value | v1 = v2 } s -> RIO<{\w1 -> IsPrev w1}, {\w1 b w2 -> UpdateDomain w2 w1 && AddValueIndex w2 v1 w1 }> s @-}
send :: Session s => Value -> Send Value s -> RIO s
send x (Send ch_s) = do
  (here, there) <- (liftRIO newS)
  liftRIO $ send' ch_s (x, there)
  return here

{-@ assume recv :: g:Value -> Recv Value s -> RIO <{\w1 -> IsPrev w1}, {\w1 b w2 -> UpdateDomain w2 w1 && AddValueIndex w2 g w1 }> (Value, s) @-}
recv :: Value -> Recv Value s -> RIO (Value, s)
recv _ (Recv ch_r) = do
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

top = do 
  (_, w) <- (rState testing) emptyWorld
  print $ vs w

top2 = do
  print t1
  return ()

--






--