{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--ple" @-}

{-# LANGUAGE ConstraintKinds, FlexibleContexts,
             TypeFamilies, UndecidableInstances, EmptyDataDecls, ScopedTypeVariables #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE InstanceSigs #-}
module PreSessions where

import Data.Typeable
import Control.Concurrent.Chan
import Control.Concurrent

readForcedSend :: Chan (Send a t) -> IO (a, Chan t)
readForcedSend c = do
    (Send a t) <- readChan c
    return (a, t)

writeForcedRecv :: Chan (Recv a t) -> a -> Chan t -> IO ()
writeForcedRecv c a t = writeChan c (Recv a t) 

data Send a t = Send a (Chan t)
data Recv a t = Recv a (Chan t)
data End

newtype ChanSend t = C (Chan t)

send :: Chan (Send a t) -> a -> IO (Chan t)
send c x = do
    c' <- newChan
    writeChan c (Send x c')
    return c'

send' :: ChanSend (a t) -> a -> IO (Chan t)
send' c x = do
    c' <- newChan
    writeChan c (Send x c')
    return c'

recv :: Chan (Recv a t) -> IO (a, Chan t)
recv c = do
    (Recv a c') <- readChan c
    return (a, c')

close :: Chan End -> IO ()
close c = return ()

{-@ fork :: (Link s s', Dual s s') => (Chan s -> IO ()) -> IO (Chan s') @-}
fork :: (Link s s', Dual s s') => (Chan s -> IO ()) -> IO (Chan s')
fork f = do
    c <- newChan
    c' <- newChan
    forkIO $ link (c, c')
    forkIO (f c)
    return c'

class Dual s t | s -> t, t -> s where

instance (Dual t t') => Dual (Send a t) (Recv a t')
instance (Dual t t') => Dual (Recv a t) (Send a t')
instance Dual End End

class Link s s' where
    link :: (Dual s s') => (Chan s, Chan s') -> IO ()

instance (Link t t', Dual t t') => Link (Send a t) (Recv a t') where
    link (c0, c1) = do
        (x, c0') <- readForcedSend c0
        c1' <- newChan
        forkIO $ link (c0', c1')
        writeForcedRecv c1 x c1'

instance (Link t t', Dual t t') => Link (Recv a t) (Send a t') where
    link (c0, c1) = do
        (x, c1') <- readForcedSend c1
        c0' <- newChan
        forkIO $ link (c0', c1')
        writeForcedRecv c0 x c0'

instance Link End End where
    link (c0, c1) = return ()