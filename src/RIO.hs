{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt" @-}
-- {-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-pattern-inline" @-}


module RIO where

import Control.Applicative
import qualified Data.Set as Set

{-@ data RIO a <p :: World -> Bool, q :: World -> a -> World -> Bool>
      = RIO (runState :: (x:World<p> -> IO (a, World)<\w -> {v:World<q x w> | true}>))
  @-}
data RIO a  = RIO {runState :: World -> IO (a, World)}

{-@ rState :: forall <p :: World -> Bool, q :: World -> a -> World -> Bool>.
                RIO <p, q> a -> x:World<p> -> IO (a, World)<\w -> {v:World<q x w> | true}> @-}
rState (RIO f)= f

data World = W { cnt :: Int, vs :: Set.Set Entry }
{-@ data World = W { cnt :: Int, vs :: Set.Set Entry } @-}

{-@ emptyWorld :: { w:World | cnt w = 0 && Set_emp (vs w)} @-}
emptyWorld = W 0 Set.empty


{-@ data Value = N Int @-}
data Value = N Int deriving (Eq, Ord, Show)

{-@ data Entry = E { eIdx :: Int, eVal :: Value } @-}
data Entry = E { eIdx :: Int, eVal :: Value } deriving (Eq, Ord, Show)

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

{-@ setV :: v:Value -> RIO <{\x -> true}, {\w1 b w2 -> (cnt w2 = (cnt w1 + 1)) && (vs w2) = Set_cup (Set_sng (E (cnt w2) v)) (vs w1) }> Value @-}
setV :: Value -> RIO Value 
setV v = RIO $ \w -> return ((v, setV' v w))

{-@ setV' :: v:Value -> w1:World -> { w2:World | (cnt w2 = (cnt w1 + 1)) && (vs w2) = Set_cup (Set_sng (E (cnt w2) v)) (vs w1)  } @-}
setV' :: Value -> World -> World
setV' v w = W (cnt w + 1) (Set.insert (E (cnt w + 1) v) (vs w))

{-@ getV :: RIO <{\x -> true}, {\w1 b w2 -> (cnt w1 + 1) = cnt w2 && (vs w1) == (vs w2) }> () @-}
getV :: RIO () 
getV = RIO $ \(W c v) -> return ((), W (c + 1) v)

{-@ testing :: RIO<{\x -> Set_emp (vs x) && (cnt x) = 0 }, {\w1 b w2 -> (vs w2) = Set_cup (Set_sng (E 4 (N 3))) (Set_sng (E 2 (N 1))) }> () @-}
testing :: RIO ()
testing = do
  getV
  setV (N 1)
  getV
  setV (N 3)
  return ()

{-@ getW :: RIO <{\x -> true}, {\w1 s w2 -> w1 == w2 && s == w1}>  World  @-}
getW :: RIO World
getW = RIO $ \w -> return ((w, w))

{-@ getEntry :: { i:Int | i > 0 } -> RIO <{\x -> cnt x <= i }, {\w1 s w2 -> w1 == w2 && isJust(s) => Set_mem (fromJust s) (vs w1) }> (Maybe Entry) @-}
getEntry :: Int -> RIO (Maybe Entry)
getEntry i = do
  w <- getW
  return (findEntry (vs w) i)

{-@ assume findEntry :: s:Set.Set Entry -> Int -> {e: Maybe Entry | (isJust(e)) => Set_mem (fromJust e) s } @-}
findEntry :: Set.Set Entry -> Int -> Maybe Entry
findEntry s i = byIdx (Set.elems s) i

{-@ byIdx :: s:[Entry] -> Int -> {e: Maybe Entry | (isJust(e)) => Set_mem (fromJust e) (listElts s) } @-}
byIdx :: [Entry] -> Int -> Maybe Entry
byIdx ([]) _ = Nothing
byIdx (x:xs) i = if (eIdx x) == i then Just(x) else (byIdx xs i)

-- medio hacky, pero 

-- {-@ assume lookup' :: w:World -> { i:Int | cnt w <= i && i > 0 } -> {e: Entry | eIdx e = i && Set_mem e (vs w) } @-}
-- lookup' :: World -> Int -> Entry
-- lookup' (W c v) i = case Set.lookupGE (E i (N 0)) v of
--   Just a -> a
--   Nothing -> unsafeError "unreachable"
-- 
-- {-@ ignore unsafeError @-}
-- unsafeError = error
-- 

-- tlookup :: RIO (Maybe Entry)
-- tlookup = do
--   testing
--   getEntry 2