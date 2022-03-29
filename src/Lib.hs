{-@ LIQUID "--no-pattern-inline" @-}

module Lib where

import Prelude
import Control.Applicative

{-@ measure lastVal :: World -> Int @-}

{-@ predicate Pure W1 W2 = W1 = W2 @-}

{-@ assume emptyWorld :: {w:World | lastVal w = 0} @-}
emptyWorld :: World
emptyWorld = W

{-@ assume doA :: Typestate s => v1:Int -> A Int s -> RIO<{\w -> lastVal w < v1}, {\w1 b w2 -> lastVal w2 = v1}> s @-}
doA :: Typestate s => Int -> A Int s -> RIO s
doA i (A s) = do
    liftRIO $ print i
    return s

{-@ assume doB :: B s -> RIO<{\w -> true}, {\w1 v w2 -> true}> s @-}
doB :: B s -> RIO s
doB (B s) = do 
    liftRIO $ putStrLn "doing B"
    return s

{-@ end :: End -> RIO <{\x -> true}, {\w1 b w2 -> Pure w1 w2}> () @-}
end :: End -> RIO ()
end (End s) = return ()

{-@ assume selectLeft :: Typestate s => Branch s_1 s_2 -> RIO<{\w1 -> true}, {\w1 v w2 -> Pure w1 w2 }> s_1 @-}
selectLeft :: (Typestate s_1) => Branch s_1 s_2 -> RIO s_1
selectLeft (A _) = return $ newS

{-@ assume selectRight :: Typestate s => Branch s_1 s_2 -> RIO<{\w1 -> true}, {\w1 v w2 -> Pure w1 w2}> s_2 @-}
selectRight :: (Typestate s_2) => Branch s_1 s_2 -> RIO s_2
selectRight (A _) = return $ newS

newtype Rec
  = MkRec (Branch (A Int Rec) (B End))

{-@ f :: Rec -> RIO <{\w -> lastVal w = 0}> () @-}
f :: Rec -> RIO ()
f (MkRec s) = do 
    s <- selectLeft s
    MkRec s <- doA 100 s
    s <- selectLeft s
    MkRec s <- doA 100 s
    s <- selectLeft s
    MkRec s <- doA 300 s
    --s <- selectLeft s
    --MkRec s <- doA 400 s
    --s <- selectLeft s
    --MkRec s <- doA 500 s
    s <- selectRight s
    s <- doB s

    end s

mainFunc = fmap fst $ rState (f newS) $ emptyWorld 


{-@ data A a s = A s @-}
data A a s = A s

{-@ data B s = B s @-}
data B s = B s
data End      = End ()

type Branch c1 c2 = A (Either c1 c2) ()


-- recursive constructors
--
class Typestate s where
  newS :: s

instance Typestate s => Typestate (A a s) where
  newS = A newS

instance Typestate s => Typestate (B s) where
  newS = B newS

instance Typestate End where
  newS = End ()

instance Typestate () where
  newS = ()

instance Typestate Rec
  where
    newS = MkRec $ newS 


{-@ liftRIO :: IO a -> RIO<{\w -> true}, {\w1 v w2 -> w1 == w2 }> a @-}
liftRIO :: IO a -> RIO a
liftRIO m = RIO $ \w -> (fmap (\v -> (v, w)) m)

-- RIO

{-@ data RIO a <p :: World -> Bool, q :: World -> a -> World -> Bool>
      = RIO (runState :: (x:World<p> -> IO (a, World)<\w -> {v:World<q x w> | true}>))
  @-}
data RIO a  = RIO {runState :: World -> IO (a, World)}

{-@ rState :: forall <p :: World -> Bool, q :: World -> a -> World -> Bool>.
                RIO <p, q> a -> x:World<p> -> IO (a, World)<\w -> {v:World<q x w> | true}> @-}
rState (RIO f)= f

data World = W
{-@ data World = W @-}

-- | RJ: Putting these in to get GHC 7.10 to not fuss
instance Functor RIO where
  fmap = undefined

-- | RJ: Putting these in to get GHC 7.10 to not fuss
instance Applicative RIO where
  pure  = undefined
  (<*>) = undefined

instance Monad RIO where
{-@ instance Monad RIO where
      >>= :: forall < p  :: World -> Bool 
                    , p2 :: a -> World -> Bool
                    , r  :: a -> Bool
                    , q1 :: World -> a -> World -> Bool
                    , q2 :: a -> World -> b -> World -> Bool
                    , q  :: World -> b -> World -> Bool>.
           {x::a<r>, w::World<p>|- World<q1 w x> <: World<p2 x>}
           {w::World<p>, x::a<r>, w1:: World<q1 w x>, w2::{v:World<p2 x> | v == w1}, y::b|- World<q2 x w2 y> <: World<q w y>}
           {x::a, w::World<p>, w2::World<q1 w x>|- {v:a | v = x} <: a<r>}
           RIO <p, q1> a
        -> (x:a<r> -> RIO <{v:World<p2 x> | true}, \w1 y -> {v:World<q2 x w1 y> | true}> b)
        -> RIO <p, q> b ;
      >>  :: forall < p   :: World -> Bool
                    , p2  :: World -> Bool
                    , q1 :: World -> a -> World -> Bool
                    , q2 :: World -> b -> World -> Bool
                    , q :: World -> b -> World -> Bool>.
            {x::a, w::World<p>|- World<q1 w x> <: World<p2>}
            {w::World<p>, w2::World<p2>, y::a, w3:: {v:World<q1 w y> | v == w2}, x::b |- World<q2 w2 x> <: World<q w x>}
            RIO <p, q1> a
         -> RIO <p2, q2> b
         -> RIO <p, q> b  ;
      return :: forall <p :: World -> Bool>.
                x:a -> RIO <p, \w0 y -> {w1:World | w0 == w1 && y == x}> a
  @-}
  (RIO g) >>= f = RIO $ \x -> do
    (v, w) <- g x
    runState (f v) w
  return w      = RIO $ \x -> return (w, x)
