{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}

{-# LANGUAGE NoMonomorphismRestriction, PartialTypeSignatures #-}
{-# LANGUAGE ConstraintKinds, FlexibleContexts,
             TypeFamilies, UndecidableInstances, EmptyDataDecls, ScopedTypeVariables #-}

module Lib where
import Data.Typeable
import Control.Concurrent.Chan
import Control.Concurrent
import Prelude hiding (break)

mainFunc = putStrLn "Hello world"

data Send a t = Send a (Chan t)
data Recv a t = Recv a (Chan t)
data End

send :: Chan (Send a t) -> a -> IO (Chan t)
send c x = do
    c' <- newChan
    writeChan c (Send x c')
    return c'

recv :: Chan (Recv a t) -> IO (a, Chan t)
recv c = do
    (Recv a c') <- readChan c
    return (a, c')

close :: Chan End -> IO ()
close c = return ()

fork :: Link s => (Chan s -> IO ()) -> IO (Chan (Dual s))
fork f = do
    c <- newChan
    c' <- newChan
    forkIO $ link (c, c')
    forkIO (f c)
    return c'


type family
    Dual s where
    Dual (Send a t) = Recv a (Dual t)
    Dual (Recv a t) = Send a (Dual t)
    Dual End        = End


class Link s where
    link :: (Chan s, Chan (Dual s)) -> IO ()

instance Link t => Link (Send a t) where
    link (c0, c1) = do
        (Send x c0') <- readChan c0
        c1' <- newChan
        forkIO $ link (c0', c1')
        writeChan c1 (Recv x c1')

instance (Link t) => Link (Recv a t) where
    link (c0, c1) = do
        (Send x c1') <- readChan c1
        c0' <- newChan
        forkIO $ link (c0', c1')
        writeChan c0 (Recv x c0')

instance Link End where
    link (c0, c1) = return ()


-- Basic Example


{-@ data variance Recv covariant covariant @-}
{-@ data variance Send contravariant covariant @-}
{-@ data variance Chan covariant @-}

---------------------------------
--The refinement is not accepted
--{-@ client0 ::  Chan(Send {x:Int |x>0 } (Send {y:Int |y>0 } End)) -> IO() @-}
---------------------------------

{-@ client0 ::  Chan(Send {x:Int |x>0 } (Send {y:Int |y>0 } End)) -> IO() @-}
client0 :: Chan(Send Int (Send Int End)) -> IO()

client0 s0 = do
    s <- send s0 1
    s <- send s 2 --(if False then 4 else -5 :: Int)
    close s

---------------------------------
--The refinement is not accepted
--{-@ server0 :: Chan(Recv {x:Int |x>0 } (Recv Int End)) -> IO() @-}
---------------------------------

server0 :: Chan(Recv Int (Recv Int End)) -> IO()
server0 s = do
    (x, s) <- recv s
    (y, s) <- recv s
    close s
    putStrLn "End"

example0 = do
    c' <- fork server0
    client0 c'
    return ()


---------------------------------
-- Some dependencies
---------------------------------

type Ver = Bool
{-@ type Ver = {v:Bool | v == True} @-}
type Pos = Int
{-@ type Pos = {v:Int | v > 0} @-}

{-@ type Dep x  = {v:Int| x  <=> (v > 0) } @-}

{-@ type DepS x a = Send (Dep x) a  @-}

{-@ client1 :: x:Bool -> Chan(Send Bool (DepS x End)) -> IO() @-}
client1 :: Bool -> Chan(Send Bool (Send Int End)) -> IO()

client1 x s0 = do
    s <- send s0 x
-- The following is not safe
--    s <- send s (if  not x then 4 else -5 :: Int)
-- but the next one is safe
    s <- send s (if  x then 4 else -5 :: Int)
    close s

---------------------------------
-- Playing with dependent types from
--http://goto.ucsd.edu:8090/index.html#?demo=Order.hs
--http://goto.ucsd.edu/~rjhala/liquid/abstract_refinement_types.pdf
---------------------------------

-- Polymorphic Association Lists

data AssocP k v = KVP [(k, v)]


{-@ digitsP :: AssocP {v:Int | (Btwn 0 v 9)} String @-}
digitsP :: AssocP Int String
digitsP = KVP [ (1, "one")
              , (2, "two")
              , (3, "three") ]

{-@ sparseVecP :: AssocP {v:Int | (Btwn 0 v 1000)} Double @-}
sparseVecP :: AssocP Int Double
sparseVecP = KVP [ (12 ,  34.1 )
                 , (92 , 902.83)
                 , (451,   2.95)
                 , (877,   3.1 )]


{-@ predicate Btwn Lo V Hi = (Lo <= V && V <= Hi) @-}

-- Monomorphic Association Lists
-- -----------------------------

{-@ data Assoc v <p :: Int -> Bool> = KV { keyVals :: [(Int<p>, v)] } @-}
data Assoc v = KV [(Int, v)]



{-@ digits :: Assoc (String) <{\v -> (Btwn 0 v 9)}> @-}
digits    = KV [ (1, "one")
               , (2, "two")
               , (3, "three") ]


{-@ sparseVec :: Assoc (Double) <{\v -> (Btwn 0 v 1000)}> @-}
sparseVec :: Assoc Double
sparseVec = KV [ (12 ,  34.1 )
               , (92 , 902.83)
               , (451,   2.95)
               , (877,   3.1 )]


-- Dependent Tuples via Abstract Refinements
-- 
-- data (a,b)<p :: a -> b -> Prop> = (x:a, b<p x>)

-- Instantiate the `p` in *different* ways.

{-@ plusOnes :: [(Int, Int)<{\x1 x2 -> x2 = x1 + 1}>] @-}
plusOnes :: [(Int,Int)]
plusOnes = [(0,1), (5,6), (999,1000)]

{-@ plusO :: [(Bool, Int)<{\x1 x2 -> x1 = (x2 > 0)}>] @-}
plusO :: [(Bool,Int)]
plusO = [(True,1), (False,-6), (True, 1000)]

{-@ type IncrList a = [a]<{\xi xj -> xi <= xj}> @-}
{-@ type DecrList a = [a]<{\xi xj -> xi >= xj}> @-}
{-@ type UniqList a = [a]<{\xi xj -> xi /= xj}> @-}

{-@ whatGosUp :: IncrList Integer @-}
whatGosUp :: [Integer]
whatGosUp = [1,2,3]


{-@ mustGoDown :: DecrList Integer @-}
mustGoDown :: [Integer]
mustGoDown = [3,2,1]


{-@ noDuplicates :: UniqList Integer @-}
noDuplicates :: [Integer]
noDuplicates = [1,3,2]


---------------------------------
-- My attempts with dependent types
---------------------------------

data MiList a  = Null | Cons a (MiList a)

{-@ data MiList a <p :: a -> a -> Bool>
      = Null
      | Cons (h :: a) (t :: MiList <p> (a<p h>))
  @-}


{-@ type IncrListM a = MiList <{\xi xj -> xi <= xj}> a @-}

{-@ l1::IncrListM Int
@-}
l1 :: MiList Int
l1 = Cons 2 (Cons 3 Null)

data Abz a  =  Ab a

{-@ l:: Abz (Int,Int) <{\x y -> x = y+1}>
@-}
l :: Abz (Int,Int)
l = Ab (6, 5)


---------------------------------
-- Failed attempts with dependent sessions
---------------------------------

payload :: Send a t -> a
payload (Send x _) = x
{-@ measure payload @-}

{-@ data Send a t  <p :: a ->t-> Bool>
      = Send (x::a) (Chan (t <p x>) )
@-}

{-@ type DepSend a t = Send <{\xi xj -> xi = (payload xj)}> a t @-}

---------------------------------
-- Safe but wrong,
-- I suspect the problem is in the pattern Chan (t <p x>) 
---------------------------------
{-@ client2 ::  Chan(DepSend Int (Send Int End)) -> IO() @-}
client2 :: Chan(Send Int (Send Int End)) -> IO()

client2 s0 = do
    s <- send s0 3
    s <- send s 2 --(if False then 4 else -5 :: Int)
    close s


-- new example 

data SS a t = S a (Maybe t)
data RR a t = R a (Maybe t)
data E = E

{-@ measure ps @-}
ps :: SS a t -> a
ps (S x _) = x

{-@ data SS a t  <p :: a -> t-> Bool> = S (y::a) (Maybe (t <p y>)) @-}
{-@ type DSS a t = SS <{\xi xj -> xi = (ps xj)}> a t @-}

{-@ testS :: DSS Int (DSS Int (SS Int E)) @-}
testS :: SS Int (SS Int (SS Int E))
testS = S 1 (Just (S 1 (Just (S 1 Nothing))))