-- {-@ LIQUID "--prune-unsorted" @-}
-- {-@ LIQUID "--ple" @-}
-- {-@ LIQUID "--reflection" @-}

{-@ LIQUID "--no-adt" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-pattern-inline" @-}
-- {-@ LIQUID "--exact-data-cons" @-}
-- 
-- 
module RIO where

import Control.Applicative
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map (Map)

{-@ data RIO a <p :: World -> Bool, q :: World -> a -> World -> Bool>
      = RIO (runState :: (x:World<p> -> IO (a, World)<\w -> {v:World<q x w> | true}>))
  @-}
data RIO a  = RIO {runState :: World -> IO (a, World)}

{-@ rState :: forall <p :: World -> Bool, q :: World -> a -> World -> Bool>.
                RIO <p, q> a -> x:World<p> -> IO (a, World)<\w -> {v:World<q x w> | true}> @-}
rState (RIO f)= f

data World = W { cnt :: Int, vs :: Values }
{-@ data World = W { cnt :: Int, vs :: Values } @-}

{-@ liftRIO :: IO a -> RIO<{\w -> true}, {\w1 v w2 -> w1 == w2 }> a @-}
liftRIO :: IO a -> RIO a
liftRIO m = RIO $ \w -> (fmap (\v -> (v, w)) m)

{-@ emptyWorld :: { w:World | cnt w = 0 && Set_emp (listElts (vdom (vs w))) && vdom (vs w) = [] } @-}
emptyWorld = W 0 emptyD

-- {-@ measure getN @-}
-- {-@ getN :: {v:Value | isN v} -> Int @-}
-- getN :: Value -> Int
-- getN (N i) = i
-- 
-- {-@ measure isN @-}
-- isN :: Value -> Bool
-- isN (N _) = True

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


{-@ predicate IsPrev W = not (Set_mem (cnt W + 1) (listElts (vdom (vs W)))) @-}
{-@ predicate IncreaseCnt A B = (cnt A) == (cnt B) + 1 @-}
{-@ predicate AddCntToDomain W2 W1 = (listElts (vdom (vs W2))) = Set_cup (Set_sng (cnt W2)) (listElts (vdom (vs W1))) @-}
{-@ predicate UpdateDomain W2 W1 = IncreaseCnt W2 W1 && AddCntToDomain W2 W1 @-}
{-@ predicate AddValueIndex W2 V W1 = (vmap (vs W2)) = Map_store (vmap (vs W1)) (cnt W2) V @-}
{-@ predicate EmptyWorld W = (vdom (vs W)) = [] && (cnt W) = 0 @-}
{-@ predicate Pure W1 W2 = W1 == W2 @-}

-- TODO: setV y setV' tienen el mismo predicado, extraerlo
{-@ setV :: v:Int -> RIO <{\w -> IsPrev w }, {\w1 b w2 -> 
      UpdateDomain w2 w1 &&
      AddValueIndex w2 v w1
      }> Int @-}
setV :: Int -> RIO Int 
setV v = RIO $ \w -> return ((v, setV' v w))

{-@ setV' :: v:Int -> {w1:World | IsPrev w1 } -> { w2:World | 
      UpdateDomain w2 w1 &&
      AddValueIndex w2 v w1
      } @-}
setV' :: Int -> World -> World
setV' v w = W (cnt w + 1) (setD (cnt w + 1) v (vs w))

{-@ getV :: RIO <{\x -> IsPrev x }, {\w1 b w2 -> IncreaseCnt w2 w1 && (vs w1) == (vs w2) }> () @-}
getV :: RIO () 
getV = RIO $ \(W c v) -> return ((), W (c + 1) v)

-- {-@ testing :: RIO<{\x -> (vdom (vs x)) = [] && (cnt x) = 0 }, {\w1 b w2 -> 
--       (listElts (vdom (vs w2))) = Set_cup (Set_sng 4) (Set_sng 2) && 
--       fromN (Map_select (vmap (vs w2)) 4) = fromN (Map_select (vmap (vs w2)) 2) + 2
--       }> ()  
--       @-}
-- testing :: RIO ()
-- testing = do
--   getV
--   setV (N 1)
--   getV
--   setV (N 3)
--   return ()

{-
  diccionario (mayormente) no chequeado
  la implementación tiene assume para las propiedades, porque

  a) no es lo que me importa realmente para esto 
  
  b) no estoy seguro de que se pueda escribir sin tener que reimplementar los
  mapas de alguna forma 
  
  c) todavía no estoy del todo seguro de cual es la semántica de Map_select si
  no hay nada insertado, o sea, podría usar Maybe, pero es medio molesto.

  d) a fin de cuentas la implementación no importa porque no se va a usar el
  valor, podría ser simplemente Nops, lo único que me importa es tener los
  refinements. Supongo que se podrían escribir puramente en términos de measures
  abstractas, pero no probé mucho eso, y tener una implementación es lindo para
  print-debuggear
-}
{-@ embed Map as Map_t @-}

{-@ measure Map_union   :: Map k v -> Map k v -> Map k v @-}
{-@ measure Map_select  :: Map Int v -> Int -> Int     @-}
{-@ measure Map_store   :: Map k v -> k -> v -> Map k v @-}

data Values = V { vdom :: [Int], vmap :: Map.Map Int Int } deriving Show
{-@ data Values = V { vdom :: [Int], vmap :: Map Int Int } @-}

{-@ assume getD :: k:Int -> {vs:Values | Set_mem k (listElts (vdom vs))} -> {v:Int | v = Map_select (vmap vs) k} @-}
getD :: Int -> Values -> Int 
getD k d = case (Map.lookup k (vmap d)) of 
  Just v -> v
  Nothing -> unreachableUnchecked

{-@ assume getD2 :: k:Int -> vs:Values -> {v:Int | v = Map_select (vmap vs) k} @-}
getD2 :: Int -> Values -> Int 
getD2 k d = case (Map.lookup k (vmap d)) of 
  Just v -> v
  Nothing -> unreachableUnchecked

{-@ ignore unreachableUnchecked @-}
unreachableUnchecked = error "unreachable"

{-@ assume setD :: k:Int -> v:Int -> {vs:Values | not (Set_mem k (listElts (vdom vs)))} -> { r:Values | 
      (vmap r) = Map_store (vmap vs) k v && 
      (listElts (vdom r)) = Set_cup (Set_sng k) (listElts (vdom vs)) } @-}
setD :: Int -> Int -> Values -> Values
setD k v vs = V (k : (vdom vs)) (Map.insert k v (vmap vs)) 

{-@ assume emptyD :: { v:Values | Set_emp (listElts (vdom v)) && vdom v = [] } @-}
emptyD :: Values
emptyD = V [] (Map.empty)

-- why doesn't this work?
-- {-@ t1 :: {s:Int | s = 3 } @-}
-- t1 :: Int
-- t1 = getD 3 $ setD 1 1 $ setD 3 3 emptyD
-- t1 = getD 1 $ setD 1 (N 1) $ setD 3 (N 3) emptyD -- unsafe
-- t1 = getD 1 emptyD -- unsafe

----

-- intentos de escribir un contrato con una monada, pero no logro hacer que el assert funcione 

{-@ getW :: RIO <{\x -> true}, {\w1 s w2 -> Pure w1 w2 && s == w1}>  World  @-}
getW :: RIO World
getW = RIO $ \w -> return ((w, w))

{-@ getEntry :: { i:Int | i > 0 } -> RIO <{\x -> Set_mem i (listElts (vdom (vs x))) }, 
      {\w1 s w2 -> Pure w1 w2 && s = Map_select (vmap (vs w1)) i }> Int @-}
getEntry :: Int -> RIO Int
getEntry i = do
  w <- getW
  return (getD i (vs w))

{-@ assume getEntry2 :: { i:Int | i > 0 } -> RIO <{\x -> true }, 
      {\w1 s w2 -> Pure w1 w2 && s = Map_select (vmap (vs w1)) i }> Int @-}
getEntry2 :: Int -> RIO Int
getEntry2 i = do
  w <- getW
  return (getD2 i (vs w))

{-@ rioAssert :: {v:Bool | v} -> RIO<{\w -> true}, {\w1 x w2 -> Pure w1 w2}> () @-}
rioAssert :: Bool -> RIO ()
rioAssert True = (return ())
rioAssert False = error "unreachable"


-- espacio en blanco porque a veces no puedo leer la última línea cuando abro el html






----