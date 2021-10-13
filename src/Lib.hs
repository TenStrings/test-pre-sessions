{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
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
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}

module Lib where
import Control.Concurrent (Chan, MVar, forkIO, newEmptyMVar, putMVar, takeMVar)
import Prelude
import Data.Bifunctor (Bifunctor(bimap))
import Data.Functor ((<$>))
import Control.Applicative ((<|>))
import Data.Tuple (swap)
import Control.Monad (void)

mainFunc = do
    print top
    example0

client0 s = do
    s <- send 5 s
    (y, s) <- recv s
    close s

{-@ type Odd = {i: Int | i mod 2 = 0 }@-}
{-@ type Even = {i: Int | i mod 2 = 1 }@-}

{-@ server0 :: (Recv Odd (Send Even End)) -> IO () @-}
server0 :: (Recv Int (Send Int End)) -> IO ()
server0 s = do
    (x, s) <- recv s
    s <- send (x + 1) s 
    close s

example0 = connect client0 server0

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

{-@ send :: Session s => v1:a -> Send {v2:a | v1 = v2 } s -> IO s @-}
send :: Session s => a -> Send a s -> IO s
send x (Send ch_s) = do
  (here, there) <- newS
  send' ch_s (x, there)
  return here

recv :: Recv a s -> IO (a, s)
recv (Recv ch_r) = recv' ch_r

close :: End -> IO ()
close (End s) = sync s

connect :: (Session s) => (s -> IO ()) -> (Dual s -> IO a) -> IO a
connect k1 k2 = do (s1, s2) <- newS; void (forkIO (k1 s1)); k2 s2

-- * One-shot channels

data SendOnce a = SendOnce (MVar a)
data RecvOnce a = RecvOnce (MVar a)

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

newSync :: IO (SyncOnce, SyncOnce)
newSync = do
  (ch_s1, ch_r1) <- new'
  (ch_s2, ch_r2) <- new'
  return (SyncOnce ch_s1 ch_r2, SyncOnce ch_s2 ch_r1)

sync :: SyncOnce -> IO ()
sync (SyncOnce ch_s ch_r) = do send' ch_s (); recv' ch_r

-- * Contracts

data Sop a c = Sop a c
data Rop a c = Rop c
data Nop = Nop

class Op a b c | a -> b, a -> c where
  value :: a -> Maybe b
  continuation :: a -> Maybe c 

{-@ safeOr :: v1:Maybe a -> {v2: Maybe a | isJust v1 <=> not(isJust v2) } -> a @-}
safeOr :: Maybe a -> Maybe a -> a
safeOr (Just a) _ = a
safeOr _ (Just a) = a

instance Op (Sop a c) a c where
  value (Sop a _) = Just a
  continuation (Sop _ c) = Just c

instance Op (Rop a c) a c where
  value (Rop c) = Nothing
  continuation (Rop c) = Just c

instance Op Nop () () where
  value Nop = Nothing
  continuation Nop = Nothing

{-@ unwrap :: { v: Maybe a | isJust v } -> a @-}
unwrap :: Maybe a -> a
unwrap (Just a) = a
unwrap _ = error "unreachable"

class Comb a a' c | a -> c, a -> a' where
  combine :: a -> a' -> c  

instance (Comb c c' d) => Comb (Sop v c) (Rop v c') (Contract v d) where 
  combine :: (Sop v c) -> (Rop v c') -> (Contract v d)
  combine a a' = C (safeOr (value a) (value a')) (combine (cont a) (cont a'))
    where 
      cont = unwrap . continuation

instance (Comb c c' d) => Comb (Rop v c) (Sop v c') (Contract v d) where 
  -- combine (Rop c) (Sop a c')  = C a (combine c c')
  combine = undefined

instance Comb Nop Nop (Contract () ()) where
  -- combine Nop Nop = N
  combine = undefined

{-@ data Contract a c <p :: a -> Bool, q :: a -> c -> Bool> = C { val :: a<p>, cont :: c<q val> } | N @-}
data Contract a c = C { val :: a, cont :: c } | N deriving (Eq, Show)

{-@ data variance Contract contravariant covariant @-}

{-@ test :: Contract <{\x -> True}, {\x c -> x + 1 = (val c)}> Int (Contract Int (Contract () ())) @-}
test :: Contract Int (Contract Int (Contract () ()))
test = C 1 (C 2 N)

{-@ test :: Contract <{\x -> x = 1}> Int (Contract () ()) -> () @-}
test :: Contract Int (Contract () ()) -> ()
test = combine (Sop (1 :: Int) Nop) ((Rop Nop) :: Rop Int _)
-- top = undefined


---




---