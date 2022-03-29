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

mainFunc = do
    example0


{-@ data variance Recv covariant covariant @-}
{-@ data variance Send contravariant covariant @-}

data Send a t = Send a (Chan t)
data Recv a t = Recv a (Chan t)
data End

{-@ send :: x:a -> Chan (Send {v : a  | v = x } t) -> IO (Chan t)  @-} 
send :: a -> Chan (Send a t) -> IO (Chan t)
send x c = do
    c' <- newChan
    writeChan c (Send x c')
    return c'
    
{-@ recv ::Chan (Recv a t) -> IO (a, Chan t)  @-}
recv :: Chan (Recv a t) -> IO (a, Chan t)
recv c = do
    (Recv a c') <- readChan c
    return (a, c')

close :: Chan End -> IO ()
close c = return ()

{-@ fork :: Link s => (Chan s -> IO ()) -> IO (Chan (Dual s))@-}
fork :: Link s => (Chan s -> IO ()) -> IO (Chan (Dual s))
fork f = do
    c <- newChan
    c' <- newChan
    forkIO $ link c c'
    forkIO (f c)
    return c'

newS :: Link s => IO (Chan s , Chan (Dual s))
newS  = do
    c <- newChan
    c' <- newChan
    forkIO $ link c c'
    return (c,c')


type family
    Dual s where
    Dual (Send a t) = Recv a (Dual t)
    Dual (Recv a t) = Send a (Dual t)
    Dual End        = End

class Link s where
    link :: Chan s -> Chan (Dual s) -> IO ()

instance Link t => Link (Send a t) where
    link c0  c1 = do
        (Send x c0') <- readChan c0
        c1' <- newChan
        forkIO $ link c0' c1'
        writeChan c1 (Recv x c1')

instance (Link t) => Link (Recv a t) where
    link c0 c1 = do
        (Send x c1') <- readChan c1
        c0' <- newChan
        forkIO $ link c0' c1'
        writeChan c0 (Recv x c0')

instance Link End where
    link c0 c1 = return ()


-- Basic Example
{-@ data variance Chan covariant @-}

{-@ client0 :: Chan (Send Int (Recv Int End)) -> IO() @-}
client0 :: Chan(Send Int (Recv Int End)) -> IO()
client0 s = do
    s <- send 5 s
    (y, s) <- recv s
    close s

{-@ server0 :: Chan (Recv Odd (Send Even End)) -> IO() @-}
server0 :: Chan(Recv Int (Send Int End)) -> IO()
server0 s = do
    (x, s) <- recv s
    s <- send (x+1) s -- x+2 es unsafe 
    close s
    putStrLn "End"

-- el fork no anda, no es unsound, solo lo rechaza
{-@ ignore example0 @-}
example0 = do
    c' <- fork server0
    return c'
    client0 c'
    return ()

{-@ data Contract a t <p :: a -> Bool, q :: a -> t -> Bool> = Contract {v::a<p>, cont::t<q v>} @-}
data Contract a t = Contract a t
data NC = NC

-- data Cn = Cn (a -> c)

{-@ reflect next @-}
next :: Contract a t -> a
next (Contract a _) = a

{-@ any_c :: a -> t -> Contract<{\_ -> true}, {\_ _ -> true}> a t @-}
any_c :: a -> t -> Contract a t
any_c a t = Contract a t

{-@ send_c :: forall <p :: a -> Bool>. x:a<p> -> t -> {c: Contract<p, {\_ _ -> true}> a t | (next c) == x} @-}
send_c :: a -> t -> Contract a t
send_c a t = Contract a t

{-@ send_d :: forall <p :: a -> Bool, q :: a -> t -> Bool>. x:a<p> -> t<q x> -> Contract<p, q> a t @-}
send_d :: a -> t -> Contract a t
send_d a t = Contract a t

{-@ test :: Contract <{\x -> x == 1}, {\x c -> (next c) = x + 1}> Int (Contract Int NC) @-}
test :: Contract Int (Contract Int NC)
-- test = send_d 1 (send_c 3 NC) -- esto es unsafe
test = send_d 1 (send_c 2 NC)
