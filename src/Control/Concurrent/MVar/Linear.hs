{-# LANGUAGE LinearTypes #-}

module Control.Concurrent.MVar.Linear
  ( MVar
  , newEmptyMVar
  , takeMVar
  , putMVar
  ) where

import           Prelude.Linear hiding (IO)
import           Control.Concurrent.MVar (MVar)
import qualified Control.Concurrent.MVar as MVar
import           Data.Unrestricted.Linear
import qualified System.IO.Linear as Linear
import           Unsafe.Linear as Unsafe

newEmptyMVar :: Linear.IO (Ur (MVar a))
newEmptyMVar =
  Linear.fromSystemIOU MVar.newEmptyMVar

takeMVar :: MVar a %1-> Linear.IO a
takeMVar mvar =
  Linear.fromSystemIO (Unsafe.toLinear MVar.takeMVar mvar)

{-@ putMVar :: MVar a -> a -> Linear.IO () @-}
putMVar :: MVar a %1-> a %1-> Linear.IO ()
putMVar mvar x =
  Linear.fromSystemIO (Unsafe.toLinear2 MVar.putMVar mvar x)

-- TODO: borrar esto, por ahora solo para probar que liquid no se rompa con los
-- linear types.
{-@ putMVar2 :: MVar {i:Int | i > 0} -> {i:Int | i > 0} -> Linear.IO () @-}
putMVar2 :: MVar Int %1-> Int %1-> Linear.IO ()
putMVar2 mvar x =
  Linear.fromSystemIO (Unsafe.toLinear2 MVar.putMVar mvar x)

instance Consumable (MVar a) where
  consume = Unsafe.toLinear (\_mvar -> ())
