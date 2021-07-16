{-@ LIQUID "--prune-unsorted"        @-}
{-@ LIQUID "--reflection"        @-}
{-# LANGUAGE NamedFieldPuns #-}

module Lib where
import Prelude
import qualified OneShot
import Control.Concurrent (forkIO)
import PreSessions
import Env (testIncrSession)


-- para ver que realmente funcione el oneshot
testOneShot = do
    (tx, rx) <- OneShot.new
    (a, b) <- OneShot.newSync
    forkIO $ (OneShot.send tx "hello world!" >> OneShot.sync b)
    OneShot.sync a
    OneShot.recv rx
    return ()

mainFunc = do
    testOneShot
    pingWorks
    divSession
    -- divSession'
    return testIncrSession

type Ping = Send () End
type Pong = Dual Ping

pingWorks :: IO ()
pingWorks = connect ping pong

ping :: Ping -> IO ()
ping s = do
    s <- send ((), s)
    close s

pong :: Pong -> IO ()
pong s = do
    ((), s) <- recv s
    close s

divSession :: IO ()
divSession = connect divServer divClient

data NZ = NZ Int
{-@ NZ :: {i: Int | i != 0 } -> NZ @-}

{-@toInt :: NZ -> { i: Int | i != 0 }@-}
toInt :: NZ -> Int
toInt (NZ i) = i


-- {-@ divServer :: Recv Int (Recv {i: Int | i /= 0 } (Send Int End)) -> IO () @-}
divServer :: Recv Int (Recv NZ (Send Int End)) -> IO ()
divServer s = do
    (a, s) <- recv s
    (b, s) <- recv s
    s <- send (a `div` toInt b, s)
    close s

-- {-@ divClient :: (Send Int (Send {i: Int | i /= 0} (Recv Int End))) -> IO () @-}
divClient :: (Send Int (Send NZ (Recv Int End))) -> IO ()
divClient s = do
    s <- send (2, s)
    s <- send (NZ 1, s)
    (answer, s) <- recv s
    print $ "answer is " ++ (show answer)
    close s


-- divSession' :: IO ()
-- divSession' = connect divServer divClient
--
-- divServer' :: Env -> Recv Int (Recv Int (Send Int End)) -> IO ()
-- divServer' e s = do
--     (a, s) <- recv s
--     (b, s) <- recv s
--     s <- send (a `div` (b * 2 + 1), s)
--     close s
--
-- -- {-@ divClient :: (Send Int (Send {i: Int | i /= 0} (Recv Int End))) -> IO () @-}
-- divClient' :: Env -> (Send Int (Send Int (Recv Int End))) -> IO ()
-- divClient' e s = do
--     (e, s) <- send' e "x" (2, s)
--     (e, s) <- send' e "y" (1, s)
--     (answer, s) <- recv s
--     print answer
--     close s
--
-- testExpr = print (eval empty (Equal (Number 1) (Number 1)))
