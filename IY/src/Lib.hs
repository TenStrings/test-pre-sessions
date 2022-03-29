{-# LANGUAGE FlexibleContexts, RebindableSyntax, NoMonomorphismRestriction,
             AllowAmbiguousTypes, TypeOperators #-}

module Lib where
import Control.Concurrent.FullSession
import Prelude hiding (return,(>>=),(>>))

return :: a -> Session t ss ss a
return = ireturn
(>>=) :: Session t ss tt a -> (a -> Session t tt uu b) -> Session t ss uu b
(>>=) = (>>>=)
(>>) :: Session t ss tt a -> Session t tt uu b -> Session t ss uu b
(>>) = (>>>)

{-@ type Pos= {v:Int | v > 0}@-}

newtype NonZero = NZ Int deriving (Show)
{-@ NZ :: Pos -> NonZero @-}

data AddOne = Increment { prev :: Int, newv :: Int }
{-@ Increment :: i:Int -> {j: Int | j = i + 1} -> AddOne @-}

server c = do
      x <- recv c
      send c (NZ 1) -- pasa, pero 0  o x no
      send c 1
      y <- recv c
      return ()

client c = do
   send c 0
   NZ x <- recv c
   io $ print x
   y <- recv c
   send c $ Increment y (y + 1)
   -- send c $ Increment y (y + 2) -- unsafe
   return ()

go = do
   c <- new
   forkIOs (server c)
   client c

mainFunc = runS go
