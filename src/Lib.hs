{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}


{-# LANGUAGE NoMonomorphismRestriction, PartialTypeSignatures #-}
{-# LANGUAGE ConstraintKinds, FlexibleContexts,InstanceSigs,
             TypeFamilies, UndecidableInstances, EmptyDataDecls, ScopedTypeVariables #-}

module Lib where
import Data.Typeable
import Control.Concurrent.Chan
import Control.Concurrent
import Prelude hiding (break)
import PreSessions

mainFunc = do
    putStrLn "hello world"


client0 s = do
    s <- send' 5 s
    (y, s) <- recv s
    close s

{-@ server0 :: (Recv Odd (Send Even End)) -> IO () @-}
server0 :: (Recv Int (Send Int End)) -> IO ()
server0 s = do
    (x, s) <- recv s
    s <- send' (x + 1) s 
    close s
    putStrLn "End"

-- example = connect client0 server0 

-- data Send a t = Send a (Chan t)
-- {-@ data Send a t = Send a (Chan t)   @-}
-- 
-- 
-- data Recv a t = Recv a (Chan t)
-- data End
-- 
-- {-@ send :: x:a -> Chan (Send {v : a  | v = x } t) -> IO (Chan t)  @-}
-- send ::  a -> Chan (Send a t) -> IO (Chan t)
-- send  x c = do
--     c' <- newChan
--     writeChan  c (Send x  c')
--     return c'
--     
-- {-@ recv ::Chan (Recv a t) -> IO (a, Chan t)  @-}
-- recv :: Chan (Recv a t) -> IO (a, Chan t)
-- recv c = do
--     (Recv a c') <- readChan c
--     return (a, c')
-- 
-- close :: Chan End -> IO ()
-- close c = return ()
-- 
-- {-@ fork :: Link s => (Chan s -> IO ()) -> IO (Chan (Dual s))@-}
-- fork :: Link s => (Chan s -> IO ()) -> IO (Chan (Dual s))
-- fork f = do
--     c <- newChan
--     c' <- newChan
--     forkIO $ link c c'
--     forkIO (f c)
--     return c'
-- 
-- newS :: Link s => IO (Chan s , Chan (Dual s))
-- newS  = do
--     c <- newChan
--     c' <- newChan
--     forkIO $ link c c'
--     return (c,c')
-- 
-- 
-- type family
--     Dual s where
--     Dual (Send a t) = Recv a (Dual t)
--     Dual (Recv a t) = Send a (Dual t)
--     Dual End        = End
-- 
-- class Link s where
--     link :: Chan s -> Chan (Dual s) -> IO ()
-- 
-- instance Link t => Link (Send a t) where
--     link c0  c1 = do
--         (Send x c0') <- readChan c0
--         c1' <- newChan
--         forkIO $ link c0' c1'
--         writeChan c1 (Recv x c1')
-- 
-- instance (Link t) => Link (Recv a t) where
--     link c0 c1 = do
--         (Send x c1') <- readChan c1
--         c0' <- newChan
--         forkIO $ link c0' c1'
--         writeChan c0 (Recv x c0')
-- 
-- instance Link End where
--     link c0 c1 = return ()
-- 
-- 
-- -- Basic Example
-- 
-- {-@ data variance Recv covariant covariant @-}
-- {-@ data variance Send contravariant covariant @-}
-- {-@ data variance Chan covariant @-}
-- 
-- 
-- -- {-@ client0 :: Chan (Send Odd (Recv Even End)) -> IO() @-}
-- -- client0 :: Chan (Send Int (Recv Int End)) -> IO()
-- 
-- client0 s = do
--     s <- send 5 s
--     (y, s) <- recv s
--     close s
-- 
-- {-@ server0 :: Chan (Recv Odd (Send Even End)) -> IO() @-}
-- server0 :: Chan(Recv Int (Send Int End)) -> IO()
-- server0 s = do
--     (x, s) <- recv s
--     s <- send (x+1) s -- x+2 es unsafe 
--     close s
--     putStrLn "End"
-- 
-- {-@ ignore example0 @-}
-- jxample0 = do
--     c' <- fork server0
--     return c'
--     client0 c'
--     return ()
-- 
-- ---------------------------------
-- -- Some dependencies
-- ---------------------------------
-- 
-- 
-- data C b = C { cont ::  b}
-- {-@ data C b = C { cont :: b} @-}
-- 
-- 
-- data Act a b  = Act { p :: a, c :: C b }
-- 
-- {-@ data Act a b <f :: a -> Bool, g ::a -> b -> Bool >  =
--        Act {p :: a<f p>
--            ,c :: C (b <g p>) }
-- @-}
-- 
-- 
-- {-@ myC :: Act <{\x -> x > 1},{\x y ->  x < (p y) && (p y) < (p (cont (c y)))}> Int (Act Int (Act Int Int)) @-}
-- -- {-@ myC :: Act <{\x y ->  x < (p y) && (p y) < (p (cont (c y)))}> Int (Act Int (Act Int Int)) @-}
-- myC :: Act Int (Act Int (Act Int Int))
-- myC = Act 2 (C (Act 3 (C (Act 7 (C 0)))))
-- 