{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--ple" @-}

{-# LANGUAGE GADTs                   #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE InstanceSigs            #-}
{-# LANGUAGE NoImplicitPrelude       #-}
{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeFamilyDependencies  #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module PreSessions where

import Data.Typeable
import Control.Concurrent.Chan
import Control.Concurrent
import qualified OneShot
import Data.Bifunctor (Bifunctor(bimap))
import Data.Functor ((<$>))
import Data.Tuple (swap)
import Control.Monad (void)
import GHC.Base (IO, return, (.), ($), error)

-- * Session types

newtype Send a s = Send (OneShot.SendOnce (a, Dual s))
newtype Recv a s = Recv (OneShot.RecvOnce (a, s))
newtype End      = End OneShot.SyncOnce


-- * Duality and session initiation

-- con esto ghc da stack overflow, o sea, Session (Dual s)
-- class ( Session (Dual s), Dual (Dual s) ~ s) => Session s where
class (Dual (Dual s) ~ s) => Session s where
  type Dual s = result | result -> s
  new :: IO (s, Dual s)

instance Session s => Session (Send a s) where
  type Dual (Send a s) = Recv a (Dual s)
  new = bimap Send Recv <$> OneShot.new

instance Session s => Session (Recv a s) where
  type Dual (Recv a s) = Send a (Dual s)
  new = bimap Recv Send . swap <$> OneShot.new

instance Session End where
  type Dual End = End
  new = bimap End End <$> OneShot.newSync

instance Session () where
  type Dual () = ()
  new = return ((), ())


-- * Communication primitives

send :: Session s => (a, Send a s) -> IO s
send (x, Send ch_s) = do
  (here, there) <- new
  OneShot.send ch_s (x, there)
  return here

recv :: Recv a s -> IO (a, s)
recv (Recv ch_r) = OneShot.recv ch_r

close :: End -> IO ()
close (End sync) = OneShot.sync sync

connect :: (Session s) => (s -> IO ()) -> (Dual s -> IO a) -> IO a
connect k1 k2 = do (s1, s2) <- new; void $ forkIO (k1 s1); k2 s2