-- This file defines effectful operations which encode the core operations
-- of the (session type) pi-calculus.

{-# LANGUAGE TypeOperators, DataKinds, GADTs, RankNTypes, FlexibleInstances,
              MultiParamTypeClasses, FlexibleContexts, IncoherentInstances,
              TypeFamilies, MagicHash, UnboxedTuples, ConstraintKinds #-}

{-@ LIQUID "--no-termination"       @-}
--- TODO: maybe try to remove this 

module Control.Effect.Sessions.Operations where

import Control.Effect.Sessions.Process
import Data.Type.FiniteMap

import Unsafe.Coerce
import Control.Concurrent ( threadDelay )
import qualified Control.Concurrent.Chan as C
import qualified Control.Concurrent as Conc

import Control.Monad.STM
import Control.Concurrent.STM.TMVar

import Control.Effect (Subeffect(..))

{-| A process can be run if it is /closed/ (i.e., empty channel environment) -}
run :: Process '[] a -> IO a
run = getProcess

{-| Lift IO computations to a process -}
liftIO :: IO a -> Process '[] a
liftIO = Process

{-| Print to stdout in a process -}
print :: Show a => a -> Process '[] ()
print = liftIO . (Prelude.print)

{-| putStrLn in a process -}
putStrLn = liftIO . Prelude.putStrLn

-- The simplest operations, send and receive of primitive values,
-- take a named channel 'Chan c' and return a 'Process' computation
-- indexed by the session environment '[c :-> S]' where 'S' is either a
-- send or receive action (terminated by 'End').

{-| Send a primitive-typed value -}
send :: Chan c -> t -> Process '[c :-> t :! End] ()
send (MkChan c) t = Process $ C.writeChan (unsafeCoerce c) t 

{-| Receive a primitive-typed value -}
recv :: Chan c -> Process '[c :-> t :? End] t
recv (MkChan c) = Process $ C.readChan (unsafeCoerce c)

-- The 'new' combinator models $\nu$,  which takes
-- a function mapping from a pair of two channels names
-- 'Ch c' and 'Op C' to a session with behaviour 's', and creates
-- a session where any mention to 'Ch c' or 'Op c' is removed:

{-| Create a new channel and pass its two endpoints to the supplied continuation
     (the first parameter). This channel is thus only in scope for this continuation -}
new :: (Duality env c)
          =>  ((Chan (Ch c), Chan (Op c)) -> Process env t)
          ->  Process (env :\ (Op c) :\ (Ch c)) t
new f = Process $ C.newChan >>= (\c -> getProcess $ f (MkChan c, MkChan c))

{-| Parallel compose two processes, if they contain balanced sessions -}
par :: (BalancedPar env env') =>
        Process env () -> Process env' () -> Process (DisjointUnion env env') ()
par (Process x) (Process y) =  Process $ do res <- newEmptyTMVarIO
                                            res' <- newEmptyTMVarIO
                                            Conc.forkIO $ (x >>= (atomically . (putTMVar res)))
                                            Conc.forkIO $ (y >>= (atomically . (putTMVar res')))
                                            () <- atomically $ do { takeTMVar res }
                                            () <- atomically $ do { takeTMVar res' }
                                            return ()

{-| Turn all session types into 'balancing checked' session types |-}
type family AllBal (env :: [Map Name Session]) :: [Map Name Session] where
            AllBal '[] = '[]
            AllBal ((c :-> s) ': env) = (c :-> Bal s) ': (AllBal env)


{-| Send a channel 'd' over channel 'c' -}
chSend :: Chan c -> Chan d -> Process '[c :-> (Delg s) :! End, d :-> Bal s] ()
chSend (MkChan c) t = Process $ C.writeChan (unsafeCoerce c) t

{-| Receive a channel over a channel 'c', bind to the name 'd' -}
chRecv :: Chan c -> Process '[c :-> (Delg (env :@ d)) :? End]
                        ((Chan d -> Process env a) -> Process (env :\ d) a)
chRecv (MkChan c) = Process $ return $
                               \f -> let y = (C.readChan (unsafeCoerce c) >>=
                                                     (getProcess . f . unsafeCoerce))
                                     in Process $ y


instance Subeffect Process env env' =>
         Subeffect Process ((c :-> s) ': env) ((c :-> s :+ t) ': env') where
    sub (Process p) = Process p

instance Subeffect Process env env' =>
         Subeffect Process ((c :-> t) ': env) ((c :-> s :+ t) ': env') where
    sub (Process p) = Process p

instance Subeffect Process env env where
    sub = id

instance Subeffect Process env env' =>
         Subeffect Process ((c :-> s) ': env) ((c :-> s) ': env') where
    sub (Process p) = Process p

instance Subeffect Process env env' =>
         Subeffect Process env ((c :-> End) ': env') where
    sub (Process p) = Process p

{-| Explicit subeffecting introduction of ':+' with the current session behaviour on the left -}
subL :: Process '[c :-> s] a -> Process '[c :-> s :+ t] a
subL = sub

{-| Explicit subeffecting introduction of ':+' with the current session behaviour on the right -}
subR :: Process '[c :-> t] a -> Process '[c :-> s :+ t] a
subR = sub

{-| Explicit subeffecting introduction of a terminated session for channel 'c' -}
subEnd :: Chan c -> Process '[] a -> Process '[c :-> End] a
subEnd _ = sub

instance Subeffect Process '[] '[d :-> s] where
    sub (Process p) = Process p

caseUnion :: Chan c -> Process env a -> Process ((c :-> s) ': env) a
caseUnion _ (Process p) = Process p

{-| Recursion combinator for recursive functions which have an affine fixed-point
    equation on their effects.
      For example, if 'h ~ (Seq h a) :+ b' then 'ToFix h = Fix a b,'
   -}
affineFix :: ((a -> Process '[c :-> Star] b)
          -> (a -> Process '[c :-> h] b))
          -> a -> Process '[c :-> ToFix h] b
affineFix f x = let (Process p) = f (\x' -> let (Process y) = affineFix f x' in Process y) x
                 in Process p

{-| Output a channel (dual to a replicated input) -}
rsend :: Chan c -> Chan d -> Process '[c :-> (Delg s) :*! End, d :-> Bal s] ()
rsend (MkChan c) t = Process $ C.writeChan (unsafeCoerce c) t