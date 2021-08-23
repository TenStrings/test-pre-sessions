module OneShot
  ( SendOnce
  , RecvOnce
  , new
  , send
  , recv
  -- One-shot synchronisation
  , SyncOnce
  , newSync
  , sync
  ) where

import qualified Prelude
import           Data.Proxy
import Control.Concurrent (MVar, newEmptyMVar, putMVar, takeMVar)
import GHC.Base (IO)
import Data.Bifunctor (Bifunctor(bimap))
import Prelude


-- * One-shot channels

data SendOnce a = SendOnce (MVar a)
data RecvOnce a = RecvOnce (MVar a)

{-@ data variance SendOnce covariant @-}
{-@ data variance RecvOnce covariant @-}

new :: IO (SendOnce a, RecvOnce a)
new = bimap SendOnce RecvOnce <$> dup2 newEmptyMVar
    where 
        -- In the linear version, this comes from somewhere else
        dup2 :: IO (MVar a) -> IO (MVar a, MVar a)
        dup2 first = do
            f <- first 
            return (f, f)

send :: SendOnce a -> a -> IO ()
send (SendOnce mvar) = putMVar mvar

recv :: RecvOnce a -> IO a
recv (RecvOnce mvar) = takeMVar mvar

-- * Synchronisation construct

data SyncOnce = SyncOnce (SendOnce ()) (RecvOnce ())

newSync :: IO (SyncOnce, SyncOnce)
newSync = do
  (ch_s1, ch_r1) <- new
  (ch_s2, ch_r2) <- new
  return (SyncOnce ch_s1 ch_r2, SyncOnce ch_s2 ch_r1)

sync :: SyncOnce -> IO ()
sync (SyncOnce ch_s ch_r) = do send ch_s (); recv ch_r