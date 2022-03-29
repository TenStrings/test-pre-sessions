module Control.Effect.Sessions
  ( Process (..),
    Chan (..),
    Name (..),
    Symbol,
    Session (..),
    Delegate (..),
    Dual,
    DualP,
    SessionSeq,
    Balanced,
    BalancedPar,
    NotBal,
    Effect (..),
    Control.Effect.fail,
    run,
    Map (..),
    (:@),
    Union,
    (:\),
    send,
    recv,
    new,
    par,
    print,
    putStrLn,
    liftIO,
    ifThenElse,
    UnionSeq,
    chSend, 
    chRecv,
    chRecvSeq,
    subEnd,
    subL,
    subR,
    affineFix,
    rsend,
  )
where

import Control.Effect
import Control.Effect.Sessions.Operations
import Control.Effect.Sessions.Process
import Data.Type.FiniteMap
import GHC.TypeLits
import Prelude hiding (Monad (..), print, putStrLn)

chRecvSeq c k = (chRecv c) >>= (\kf -> kf k)