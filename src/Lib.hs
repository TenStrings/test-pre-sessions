{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-pattern-inline" @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--no-adt" @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorder" @-}

{-# LANGUAGE TypeFamilyDependencies  #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FunctionalDependencies #-}

module Lib where
import Control.Concurrent (Chan, MVar, forkIO, newEmptyMVar, putMVar, takeMVar)
import Prelude
import Data.Bifunctor (Bifunctor(bimap))
import Data.Functor ((<$>))
import Control.Applicative ((<|>))
import Data.Tuple (swap)
import Control.Monad (void)
import RIO (RIO (RIO), rState, World (cnt, vs, W), emptyWorld, liftRIO, setV, vmap, vdom, getEntry, rioAssert, getLastEntry, Value(..), toInt, isInt, getW, setW, getD)
import qualified Data.Set as Set
import qualified Data.Set as Map
import Data.Map (Map)

mainFunc = do
    putStrLn "hello world"
    incrS

{-@ client :: (Send Value (Recv Value End)) -> RIO <{\w -> EmptyWorld w}> () @-}
client :: (Send Value (Recv Value End)) -> RIO ()
client s = do
    w1 <- getW

    s <- send (I 5) s

    -- Esto no funciona porque estoy chequeando por igualdad... en realidad lo
    -- que me gustaría es chequear por subtipo, pero no creo que se pueda.
    --
    -- Supongo que lo que tendría sentido realmente es chequear en la
    -- poscondición con un predicado (como estoy haciendo actualmente)... El
    -- tema es que no hay forma trivial de reusar eso para llenar los valores
    -- del otro lado de la sesión. Principalmente porque uno es un predicado
    -- sobre el estado final y lo que necesito para "llenar" el otro lado son
    -- predicados sobre estados parciales.
    --
    -- La otra forma es que el contrato no diga anyInt si no (I 5), pero
    -- ahí medio que estaría sobrespecificando realmente
    --
    -- sent <- getLastEntry
    -- rioAssert $ clientC w1 == sent

    -- tampoco sé cómo encapsular esto
    w <- getW
    expect $ serverC w

    (y, s) <- recv s

    -- solo para chequear que no rompí nada, serverC ya verifica esto en
    -- principio (o sea, es más que nada para verificar que se pueden usar los
    -- refinements del contrato acá adentro)
    x <- getEntry 1
    rioAssert $ (toInt y) == (toInt x) + 1
    -- rioAssert $ (toInt y) == (toInt x) + 2 -- unsafe
    rioAssert $ (toInt y) > 0

    close s

    -- debuging, borrar después
    -- w <- getW
    -- liftRIO $ print w


{-@ server :: (Recv Value (Send Value End)) -> RIO <{\w -> EmptyWorld w}> () @-}
server :: (Recv Value (Send Value End)) -> RIO ()
server s = do
    w <- getW
    expect $ clientC w

    (x, s) <- recv s

    w1 <- getW

    s <- send (I $ (toInt x) + 1) s 
    -- s <- send (I $ (toInt x) + 2) s -- unsafe

    -- o sea, esto funciona, pero es super hacky e incómodo, y no sé me ocurre
    -- una forma de encapsularlo/abstraerlo como para que se haga
    -- automáticamente (o al menos forzosamente)
    -- bah, se me ocurre una... template haskell por ahí, o sea, sustituciones
    -- a nivel sintáctico... digamos, es automatizable supongo, solo que no sé
    -- cómo hacerlo por no tener algo así como predicados de alto orden (si es
    -- que eso tiene sentido). 
    --
    -- O sea, reemplazar: 
    -- `s <- send a s` por 
    --  `w1 <- getW; s <- send a s; sent <- getLastEntry; rioAssert ... `
    -- sería una solución, lo preferible sería hacerlo con una función, pero no
    -- sé cómo tipar `send` en ese caso, porque no puedo usar el contrato en el
    -- refinement
    sent <- getLastEntry
    -- nótese que w1 es el 'estado' antes del último send
    rioAssert $ serverC w1 == sent

    close s


{-@ assume anyInt :: Int @-}
anyInt :: Int
anyInt = 5

incrS = connect client server


{-@ serverC :: {w:World | isInt (Map_select (vmap (vs w)) 1) && Set_mem 1 (listElts (vdom (vs w)))  }  -> {v:Value | v = (I (toInt (Map_select (vmap (vs w)) 1) + 1))} @-}
serverC :: World -> Value
-- la implementación no importa realmente, pero si pongo `undefined` crashea
-- al ejecutarlo, aunque en realidad no sé por qué si el valor no se usa (o
-- sea, el World en su enteridad no se usa). Tendría que pensarlo un poco más,
-- o entender mejor la lazyness de haskell supongo.
serverC w = I $ (toInt $ getD 1 (vs w)) + 1
-- serverC w = undefined
--

{-
 Otra opción es escribirlo directamente como monada, y se puede embeber
 directamente en el cliente... el tema es que en el server no tiene sentido
 Podría escribir el predicado de manera que diga que si el valor ya existe es X
 y si no existe inserto X, y ahí se podría usar en los dos, pero no sé qué
 tanto sentido tendría (o sea, no sé si es muy distinto a escribir dos predicados diferentes).
 Me gustaría algo un poco menos error-prone
{-@ serverC :: RIO <
        {\w -> IsPrev w && Set_mem 1 (listElts (vdom (vs w))) && isInt (Map_select (vmap (vs w)) 1) && cnt w = 1 },
        {\w1 x w2 -> AddValue w2 (I (toInt (Map_select (vmap (vs w2)) 1) + 1)) w1 }> ()
@-}
serverC :: RIO ()
serverC = do 
    x <- getEntry 1
    setV $ I ((toInt x) + 1)

    return ()

-}

{-@ clientC :: w:World  -> {v:Value | isInt v} @-}
clientC :: World -> Value
clientC w = I anyInt

-- * Session types

{-@ data Send a s = Send (SendOnce (a, Dual s)) @-}
data Send a s = Send (SendOnce (a, Dual s))
{-@ data Recv a s = Recv (RecvOnce (a, s)) @-}
data Recv a s = Recv (RecvOnce (a, s))
data End      = End SyncOnce

{-@ data variance Recv covariant covariant @-}
{-@ data variance Send contravariant covariant @-}


-- * Duality and session initiation

-- con esto ghc da stack overflow, o sea, Session (Dual s)
-- class ( Session (Dual s), Dual (Dual s) ~ s) => Session s where
class (Dual (Dual s) ~ s) => Session s where
  type Dual s = result | result -> s
  newS :: IO (s, Dual s)

instance Session s => Session (Send a s) where
  type Dual (Send a s) = Recv a (Dual s)
  newS = bimap Send Recv <$> new'

instance Session s => Session (Recv a s) where
  type Dual (Recv a s) = Send a (Dual s)
  newS = bimap Recv Send . swap <$> new'

instance Session End where
  type Dual End = End
  newS = bimap End End <$> newSync

instance Session () where
  type Dual () = ()
  newS = return ((), ())


-- * Communication primitives

{-@ send :: Session s => v1:Value -> Send {v2:Value | v1 = v2 } s -> RIO<{\w1 -> IsPrev w1}, {\w1 b w2 -> AddValue w2 v1 w1 }> s @-}
send :: Session s => Value -> Send Value s -> RIO s
send x (Send ch_s) = do
  setV x -- add value to the environment
  (here, there) <- (liftRIO newS)
  liftRIO $ send' ch_s (x, there)
  return here


{-@ expect :: g:Value -> RIO <{\w1 -> IsPrev w1}, {\w1 b w2 -> AddValue w2 g w1 }> () @-}
expect :: Value -> RIO ()
expect v = do 
  setV v
  return ()

{-@ assume recv :: Recv Value s -> RIO <{\w1 -> cnt w1 >= 1}, {\w1 b w2 -> w1 = w2 && (fst b) = Map_select (vmap (vs w1)) (cnt w1) }> (Value, s) @-}
recv :: Recv Value s -> RIO (Value, s)
recv (Recv ch_r) = do
  liftRIO $ recv' ch_r

{-@ close :: End -> RIO <{\x -> true}, {\w1 b w2 -> w1 = w2}> () @-}
close :: End -> RIO ()
close (End s) = liftRIO $ sync s

{-@ connect :: (Session s) => (s -> RIO <{\w -> EmptyWorld w}> ()) -> (Dual s -> RIO <{\w -> EmptyWorld w}> a) -> IO a @-}
connect :: (Session s) => (s -> RIO ()) -> (Dual s -> RIO a) -> IO a
connect k1 k2 = do 
  (s1, s2) <- newS
  void (forkIO (gi (k1 s1)))
  gi (k2 s2)
  where gi rio = let io = rState rio $ emptyWorld in fmap fst io

-- * One-shot channels

data SendOnce a = SendOnce (MVar a)
data RecvOnce a = RecvOnce (MVar a)

{-@ data SendOnce a = SendOnce (MVar a) @-}
{-@ data RecvOnce a = RecvOnce (MVar a) @-}

{-@ data variance SendOnce covariant @-}
{-@ data variance RecvOnce covariant @-}

new' :: IO (SendOnce a, RecvOnce a)
new' = bimap SendOnce RecvOnce <$> dup2 newEmptyMVar
    where 
        -- In the linear version, this comes from somewhere else
        dup2 :: IO (MVar a) -> IO (MVar a, MVar a)
        dup2 first = do
            f <- first 
            return (f, f)

send' :: SendOnce a -> a -> IO ()
send' (SendOnce mvar) = putMVar mvar

recv' :: RecvOnce a -> IO a
recv' (RecvOnce mvar) = takeMVar mvar

-- -- * Synchronisation construct

data SyncOnce = SyncOnce (SendOnce ()) (RecvOnce ())

{-@ ignore newSync @-}
newSync :: IO (SyncOnce, SyncOnce)
newSync = do
  (ch_s1, ch_r1) <- new'
  (ch_s2, ch_r2) <- new'
  return (SyncOnce ch_s1 ch_r2, SyncOnce ch_s2 ch_r1)

sync :: SyncOnce -> IO ()
sync (SyncOnce ch_s ch_r) = do send' ch_s (); recv' ch_r


-- -- *

-- Experimentos con sesiones recursivas, por ahora están ignoradas porque
-- todavía no se me ocurre cómo hacer que funcione
--
-- type Select s_1 s_2 = Send (Either (Dual s_1) (Dual s_2)) ()
-- type Offer s_1 s_2 = Recv (Either s_1 s_2) ()
-- 
-- 
-- newtype SumSrv
--   = MkSumSrv (Offer (Recv Value SumSrv) (Send Value End))
-- newtype SumCnt
--   = MkSumCnt (Select (Send Value SumCnt) (Recv Value End))
-- 
-- -- sumSrv :: Int -> SumSrv -> RIO ()
-- -- sumSrv tot (MkSumSrv s) = offerEither s $ \x -> case x of
-- --   Left   s -> do expect (I anyInt); (x, s) <- recv s; sumSrv (tot + (toInt x)) s
-- --   Right  s -> do s <- send (I tot) s; close s
-- 
-- {-@ ignore sumSrv @-}
-- {-@ sumSrv :: i:Int -> SumSrv -> RIO<{\w -> i = 0 => EmptyWorld w && i > 0 => IsPrev w}> () @-}
-- sumSrv :: Int -> SumSrv -> RIO ()
-- sumSrv tot (MkSumSrv s) = offerEither s $ \x -> case x of
--   Left   s -> sumSrvLeft tot s
--   Right  s -> do s <- send (I tot) s; close s
-- 
-- {-@ ignore sumSrvLeft @-}
-- {-@ sumSrvLeft :: Int -> (Recv Value SumSrv) -> RIO<{\w -> IsPrev w}> () @-}
-- sumSrvLeft :: Int -> (Recv Value SumSrv) -> RIO ()
-- sumSrvLeft tot s = do 
--   expect (I anyInt)
--   (x, s) <- recv s
--   sumSrv (tot + (toInt x)) s
-- 
-- {-@ sumCnt :: SumCnt -> RIO <{\w -> EmptyWorld w}> () @-}
-- sumCnt :: SumCnt -> RIO ()
-- sumCnt (MkSumCnt s) = do
--     s <- selectLeft s
--     MkSumCnt s <- send (I 1) s
--     s <- selectLeft s
--     MkSumCnt s <- send (I 100) s
--     s <- selectRight s
--     expect $ (I 101)
--     (tot, s) <- recv s
-- 
--     close s
-- 
-- instance Session SumSrv
--   where
--     type Dual SumSrv = SumCnt
--     newS = do 
--         (ch_srv, ch_cnt) <- newS
--         return (MkSumSrv ch_srv, MkSumCnt ch_cnt)
-- 
-- instance Session SumCnt
--   where
--     type Dual SumCnt = SumSrv
--     newS = do
--         (ch_cnt, ch_srv) <- newS
--         return (MkSumCnt ch_cnt, MkSumSrv ch_srv)
-- 
-- 
-- sumSesh = connect sumCnt (sumSrv 0)
--
-- {-@ selectLeft :: Session s => Select s_1 s_2 -> RIO<{\w1 -> IsPrev w1}, {\w1 b w2 -> AddValue w2 L w1 }> s_1 @-}
-- selectLeft :: (Session s_1) => Select s_1 s_2 -> RIO s_1
-- selectLeft (Send s) = do 
--   setV L
--   (here, there) <- (liftRIO newS)
--   liftRIO $ send' s (Left there, ())
--   return here
-- 
-- {-@ selectRight :: Session s => Select s_1 s_2 -> RIO<{\w1 -> IsPrev w1}, {\w1 b w2 -> AddValue w2 R w1 }> s_2 @-}
-- selectRight :: (Session s_2) => Select s_1 s_2 -> RIO s_2
-- selectRight (Send s) = do 
--   setV R
--   (here, there) <- (liftRIO newS)
--   liftRIO $ send' s (Right there, ())
--   return here
-- 
-- {-@ offerEither :: forall <p :: World -> Bool, q :: World -> a -> World -> Bool>. Offer s_1 s_2 -> (Either s_1 s_2 -> RIO<p, q> a) -> RIO<p, q> a @-}
-- offerEither ::  Offer s_1 s_2 -> (Either s_1 s_2 -> RIO a) -> RIO a
-- offerEither (Recv s) match = do 
--     (e, ()) <- (liftRIO $ recv' s)
--     match e

