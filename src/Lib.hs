{-# LANGUAGE FlexibleContexts, NoMonomorphismRestriction, AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}

{-@ LIQUID "--prune-unsorted"        @-}

module Lib where
import Prelude
import Control.Concurrent (Chan, newChan, forkIO, writeChan, readChan)
import PreSessions (Recv, Send, End, send, recv, close, fork, Link (link), Dual)

{-@ type BF = { v: Bool | not v } @-}

-- {-@ client1 :: (Chan (Recv BF (Send BF End))) -> IO () @-}
-- client1 :: Chan (Recv Bool (Send Bool End)) -> IO ()
client1 s0 = do
    (v,s) <- recv s0
    s <- send s v
    close s

-- {-@ client1 :: (Chan (Recv Bool (Send BF End))) -> IO () @-}
--    s <- send s True


-- También podés tipar el server1

-- {-@ server1 :: (Chan (Send BF (Recv BF End))) -> IO () @-}
server1 s = do
    s <- send s False
    (b, s) <- recv s
    close s
    putStrLn $ if b then show b else "None"

-- Pero el problema es en el fork. Hay algo en la noción de subtipado que no se combina bien con LH.

-- mainFunc = print "hello"

-- Por ejemplo, si haces esto
-- mainFunc = do
--    c' <- fork client1
--    server1 c'
-- no pasa las constraint. Esto hay que pensarlo bien:

-- mainFunc = do
--    c <- newChan 
--    client1 c

{-@ clientS :: Chan (Recv { i: Int | i == 5 } End) -> IO () @-}
-- clientS :: Chan (Recv Int End) -> IO ()
clientS s0 = do
    (v,s) <- recv s0
    printFive v
    close s

-- {-@ serverS :: Chan (Send {i: Int | i == 5} End) -> IO () @-}
-- serverS :: Chan (Send Int End) -> IO ()
serverS s = do
    s <- send s 5
    close s

mainFunc = do
    c' <- fork2 clientS
    serverS c'

-- {-@ fork2 :: (Link s s', Dual s s') => (Chan { s: Int | s == 5 } -> IO ()) -> IO (Chan s') @-}
fork2 :: (Link s s', Dual s s') => (Chan s -> IO ()) -> IO (Chan s')
fork2 f = do
    c <- newChan
    c' <- newChan
    forkIO $ link (c, c')
    forkIO (f c)
    return c'

{-@ printFive :: { i:Int | i == 5 }  -> IO () @-}
printFive :: Int -> IO ()
printFive = print

-- mainFunc' :: IO ()
-- mainFunc' = do
--     c <- newChan
--     writeChan c 5
--     -- writeChan c 4 -- agregando esto no pasa
--     -- writeChan c 5 -- pero agregando esto sí
--     f <- readChan c
--     printFive f

mainFunc'' :: IO ()
mainFunc'' = do
    c <- newChan
    c' <- newChan
    forkIO $ link' c c'
    -- forkIO $ writeChan c 4 -- esto falla
    forkIO $ writeChan c 5
    v <- readChan c'
    printFive v

link' :: Chan a -> Chan a -> IO ()
link' c c' = do
    v <- readChan c
    writeChan c' v

newtype B1 a = B1 a
newtype B2 a = B2 a

class Wrapper ( c :: * -> * ) where
    unwrap :: c a -> a
    wrap :: a -> c a

instance Wrapper B1 where
    unwrap (B1 a) = a
    wrap a = B1 a

instance Wrapper B2 where
    unwrap (B2 a) = a
    wrap a = B2 a

newtype ChannelWrapper a ( b :: * -> * ) = C (Chan (b a))

readWrapped :: (Wrapper b) => ChannelWrapper a b -> IO a
readWrapped (C a) = unwrap <$> readChan a

writeWrapped :: (Wrapper b) => ChannelWrapper a b -> a -> IO ()
writeWrapped (C a) = writeChan a . wrap

newWrapped :: IO (ChannelWrapper a b)
newWrapped = C <$> newChan

type family
    DualB ( s :: * -> * ) where
    DualB B1 = B2
    DualB B2 = B1

-- mainFunc :: IO ()
-- mainFunc = do
--     c <- newWrapped
--     c' <- newWrapped
--     forkIO (linkB c c')
--     forkIO (writeWrapped c 4)
--     v <- readWrapped c'
--     printFive v

-- linkB :: ChannelWrapper a B1 -> ChannelWrapper a (DualB B1) -> IO ()
linkB :: ChannelWrapper a B1 -> ChannelWrapper a B2 -> IO ()
linkB c c' = do
    v <- readWrapped c
    writeWrapped c' v 