{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-pattern-inline" @-}
{-@ LIQUID "--no-adt" @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--diffcheck" @-}

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
import RIO (RIO (RIO), rState, World (W), liftRIO)
import qualified Data.Set as Set
import qualified Data.Set as Map
import Data.Map (Map)
import Unsafe.Coerce (unsafeCoerce)

mainFunc = do
    putStrLn "running session examples"
    ex1
    sumSesh
    minSesh

-- variables de estado

{-@ measure lastVal :: World -> Int @-}
{-@ measure lastLastVal :: World -> Int @-}
{-@ measure sum :: World -> Int @-}
{-@ measure sent :: World -> Set Int @-}
{-@ measure min :: World -> Int @-}

-- estado inicial (inicialización)
--
{-@ predicate EmptyWorld W = sum W = 0 && lastVal W = 0 && lastLastVal W = 0 && min W = maxInt && Set_emp (sent W) @-}

-- transiciones para cada variable de estado

{-@ predicate LastValT W1 V W2 = lastLastVal W2 = lastVal W1 && lastVal W2 = V @-}
{-@ predicate SumT W1 V W2 = sum W2 = V + (sum W1) @-}
{-@ predicate MinT W1 V W2 = min W2 = cmin V (min W1) @-}
{-@ predicate SentT W1 V W2 = sent W2 = Set_cup (Set_sng V) (sent W1) @-}

-- conjunción de las anteriores
{-@ predicate NextWorld W1 V W2 = LastValT W1 V W2 && SumT W1 V W2 && MinT W1 V W2 && SentT W1 V W2 @-}

-- constraints específicos para cada tag

{-@ predicate AscP W V = lastVal W < V @-}
{-@ predicate SumP W V = V = sum W @-}
{-@ predicate MinP W V = V = min W @-}
{-@ predicate LinearEqP W V = (lastVal W + lastLastVal W) * V = 100 @-}
{-@ predicate UniqP W V = not (Set_mem V (sent W)) @-}

-- helper
{-@ predicate Pure W1 W2 = W1 = W2 @-}


data Asc
data Sum
data Min
data Uniq
data LinearEq
data Any

{-@ inline cmin @-}
cmin :: Int -> Int -> Int 
cmin a b = if a < b then a else b 

{-@ inline maxInt @-}
maxInt :: Int
maxInt = 9223372036854775807

-- * instancias de send y recv que extienden los predicados base con los del tag
--
-- esto es básicamente generic specialization hecha a mano, debería ser
-- mecanizable. son todas iguales modulo un rename de la función, el tag y el
-- predicado (que son el mismo nombre, así que es un solo rename)
--
--

{-@ assume sendAsc :: Session s => v1:Int -> Send Asc {v2:Int | v1 = v2} s -> RIO<{\w -> AscP w v1}, {\w1 b w2 -> NextWorld w1 v1 w2}> s @-}
sendAsc :: Session s => Int -> Send Asc Int s -> RIO s
sendAsc = sendUnsafe

{-@ assume recvAsc :: Recv Asc Int s -> RIO <{\w -> true}, {\w1 v w2 -> AscP w1 (fst v) && NextWorld w1 (fst v) w2}> (Int, s) @-}
recvAsc :: Recv Asc Int s -> RIO (Int, s)
recvAsc = recvUnsafe

{-@ assume sendSum :: Session s => v1:Int -> Send Sum {v2:Int | v1 = v2} s -> RIO<{\w -> SumP w v1}, {\w1 b w2 -> NextWorld w1 v1 w2}> s @-}
sendSum :: Session s => Int -> Send Sum Int s -> RIO s
sendSum = sendUnsafe

{-@ assume recvSum :: Recv Sum Int s -> RIO <{\w -> true}, {\w1 v w2 -> SumP w1 (fst v) && NextWorld w1 (fst v) w2}> (Int, s) @-}
recvSum :: Recv Sum Int s -> RIO (Int, s)
recvSum = recvUnsafe

{-@ assume sendMin :: Session s => v1:Int -> Send Min {v2:Int | v1 = v2} s -> RIO<{\w -> MinP w v1}, {\w1 b w2 -> NextWorld w1 v1 w2}> s @-}
sendMin :: Session s => Int -> Send Min Int s -> RIO s
sendMin = sendUnsafe

{-@ assume recvMin :: Recv Min Int s -> RIO <{\w -> true}, {\w1 v w2 -> MinP w1 (fst v) && NextWorld w1 (fst v) w2}> (Int, s) @-}
recvMin :: Recv Min Int s -> RIO (Int, s)
recvMin = recvUnsafe

{-@ assume sendLinearEq :: Session s => v1:Int -> Send LinearEq {v2:Int | v1 = v2} s -> RIO<{\w -> LinearEqP w v1}, {\w1 b w2 -> NextWorld w1 v1 w2}> s @-}
sendLinearEq :: Session s => Int -> Send LinearEq Int s -> RIO s
sendLinearEq = sendUnsafe

{-@ assume recvLinearEq :: Recv LinearEq Int s -> RIO <{\w -> true}, {\w1 v w2 -> LinearEqP w1 (fst v) && NextWorld w1 (fst v) w2}> (Int, s) @-}
recvLinearEq :: Recv LinearEq Int s -> RIO (Int, s)
recvLinearEq = recvUnsafe

{-@ assume sendUniq :: Session s => v1:Int -> Send Uniq {v2:Int | v1 = v2} s -> RIO<{\w -> UniqP w v1}, {\w1 b w2 -> NextWorld w1 v1 w2}> s @-}
sendUniq :: Session s => Int -> Send Uniq Int s -> RIO s
sendUniq = sendUnsafe

{-@ assume recvUniq :: Recv Uniq Int s -> RIO <{\w -> true}, {\w1 v w2 -> UniqP w1 (fst v) && NextWorld w1 (fst v) w2}> (Int, s) @-}
recvUniq :: Recv Uniq Int s -> RIO (Int, s)
recvUniq = recvUnsafe

-- * ex 1
--

{-@ ex1Cnt :: (Send Any Int (Send Any Int (Send LinearEq Int (Recv Sum Int End)))) -> RIO<{\w -> EmptyWorld w}> () @-}
ex1Cnt :: (Send Any Int (Send Any Int (Send LinearEq Int (Recv Sum Int End)))) -> RIO ()
ex1Cnt s = do
    s <- send 20 s
    s <- send 5 s
    s <- sendLinearEq 4 s
    (y, s) <- recvSum s

    close s

-- {-@ ignore ex1Srv @-}
{-@ ex1Srv :: (Recv Any Int (Recv Any Int (Recv LinearEq Int (Send Sum Int End)))) -> RIO <{\w -> EmptyWorld w}> () @-}
ex1Srv :: (Recv Any Int (Recv Any Int (Recv LinearEq Int (Send Sum Int End)))) -> RIO ()
ex1Srv s = do
    (x, s) <- recv s
    (y, s) <- recv s
    (z, s) <- recvLinearEq s

    return $ liquidAssert $ (x + y) * z >= 100

    s <- sendSum (x + y + z) s 

    -- Lo siguiente es unsafe, pero por alguna razón también hace que el
    -- archivo de smt2 se vaya de mambo (aunque nada disparatado igual)
    -- lo cual es interesante, porque lo anterior pareciera ser fácil de
    -- verificar. 
    -- Puede ser un tema de cómo maneja la aritmética, y no el mismo
    -- problema que el otro.
    -- s <- sendSum (x + y + z + 1) s 

    close s


ex1 = connect ex1Cnt ex1Srv

-- ex 2
-- sesión recursiva que suma los elementos que recibe, con el constraint de que
-- los números que recibe tienen que ser crecientes
--
newtype SumSrv
  = MkSumSrv (Offer (Recv Asc Int SumSrv) (Send Sum Int End))
newtype SumCnt
  = MkSumCnt (Select (Send Asc Int SumCnt) (Recv Sum Int End))

{-@ sumSrv :: tot:Int -> SumSrv -> RIO<{\w -> tot = sum w}> () @-}
sumSrv :: Int -> SumSrv -> RIO ()
sumSrv tot (MkSumSrv s) = offerEither s $ \x -> case x of
  Left   s -> do (x, s) <- recvAsc s; sumSrv (tot + x) s
  Right  s -> do s <- sendSum tot s; close s

{-@ sumCnt :: xs:[Int]<{\a b -> a < b}> -> SumCnt -> RIO<{\w -> lastVal w < head xs}> () @-}
sumCnt :: [Int] -> SumCnt -> RIO ()
sumCnt (x:xs) (MkSumCnt s) = do
    s <- selectLeft s
    MkSumCnt s <- sendAsc x s
    -- no tengo ni idea de por qué agregar esto hace que ande o sea, imagino
    -- que escribirlo hace que materialize el refinement, pero esperaría que lo
    -- haga sin esto. No es algo que no haya visto antes en compiladores
    -- normales igual (poner asserts para eliminar bound checks, por ejemplo),
    -- pero pareciera ser un bug (aunque no es unsoudness, así que no es tan
    -- grave)
    assertLastValueIs x
    sumCnt xs (MkSumCnt s)
sumCnt [] (MkSumCnt s) = do
    s <- selectRight s
    (tot, s) <- recvSum s
    liftRIO $ print tot
    close s

{-@ sumCntBad :: SumCnt -> RIO <{\w -> EmptyWorld w}> () @-}
sumCntBad :: SumCnt -> RIO ()
sumCntBad (MkSumCnt s) = do 
    s <- selectLeft s
    MkSumCnt s <- sendAsc 100 s
    s <- selectLeft s
    MkSumCnt s <- sendAsc 200 s
    -- descomentar lo siguiente hace que exploten los refinements, lo que me
    -- sugiere que el problema tiene que ver con cómo instancia los bounds o
    -- algo con el monadic bind
    -- el workaround es partir cosas en pedazos, creo (como la función de arriba)
    --
    -- s <- selectLeft s
    -- MkSumCnt s <- sendAsc 300 s
    --s <- selectLeft s
    --MkSumCnt s <- sendAsc 400 s
    --s <- selectLeft s
    --MkSumCnt s <- sendAsc 500 s
    s <- selectRight s
    (tot, s) <- recvSum s

    liftRIO $ print tot
    close s


instance Session SumSrv
  where
    type Dual SumSrv = SumCnt
    newS = do 
        (ch_srv, ch_cnt) <- newS
        return (MkSumSrv ch_srv, MkSumCnt ch_cnt)

instance Session SumCnt
  where
    type Dual SumCnt = SumSrv
    newS = do
        (ch_cnt, ch_srv) <- newS
        return (MkSumCnt ch_cnt, MkSumSrv ch_srv)


-- sumSesh = connect sumCnt1 (sumSrv 0)
sumSesh = connect (sumCnt [1, 2, 3, 4, 5, 6, 7, 27]) (sumSrv 0)


-- ex 3
-- server recursivo similar al de arriba, pero que devuelve el mínimo de los
-- números que recibe, y que require que no se le manden repetidos
--
newtype MinSrv
  = MkMinSrv (Offer (Recv Uniq Int MinSrv) (Send Min Int End))
newtype MinCnt
  = MkMinCnt (Select (Send Uniq Int MinCnt) (Recv Min Int End))

{-@ minSrv :: current_min:Int -> MinSrv -> RIO<{\w -> current_min = min w}> () @-}
minSrv :: Int -> MinSrv -> RIO ()
minSrv min (MkMinSrv s) = offerEither s $ \x -> case x of
  Left   s -> do (x, s) <- recvUniq s; minSrv (if x < min then x else min) s
  Right  s -> do s <- sendMin min s; close s

{-@ minCnt :: xs:UList Int -> MinCnt -> RIO<{\w -> not (Set_mem (head xs) (sent w))}> () @-}
minCnt :: [Int] -> MinCnt -> RIO ()
minCnt (x:xs) (MkMinCnt s) = do
    s <- selectLeft s
    MkMinCnt s <- sendUniq x s
    assertLastValueIs x
    minCnt xs (MkMinCnt s)
minCnt [] (MkMinCnt s) = do
    s <- selectRight s
    (tot, s) <- recvMin s
    liftRIO $ putStrLn $ "minimum is: " ++ (show tot)
    close s

{-@ minCntBad :: MinCnt -> RIO <{\w -> EmptyWorld w}> () @-}
minCntBad :: MinCnt -> RIO ()
minCntBad (MkMinCnt s) = do
    s <- selectLeft s
    MkMinCnt s <- sendUniq 100 s
    s <- selectLeft s
    MkMinCnt s <- sendUniq 200 s
    -- el próximo send hace que explote la cantidad de cosas a probar
    -- imagino que el problema es el diccionario
    -- s <- selectLeft s
    -- MkMinCnt s <- sendUniq 300 s
    s <- selectRight s
    (min, s) <- recvMin s

    return $ liquidAssert $ min <= 100 && min < 200

    liftRIO $ print min
    close s

instance Session MinSrv
  where
    type Dual MinSrv = MinCnt
    newS = do 
        (ch_srv, ch_cnt) <- newS
        return (MkMinSrv ch_srv, MkMinCnt ch_cnt)

instance Session MinCnt
  where
    type Dual MinCnt = MinSrv
    newS = do
        (ch_cnt, ch_srv) <- newS
        return (MkMinCnt ch_cnt, MkMinSrv ch_srv)


-- minSesh = connect minCnt1 (minSrv maxInt)
minSesh = connect (minCnt [100, 200, 150, 250, 300, 350, 1]) (minSrv maxInt)

{-@ measure dups @-}
dups :: [Int] -> Set.Set Int 
dups []        = Set.empty
dups (x:xs) = if Set.member x (elements xs) then Set.singleton x `Set.union` dups xs else dups xs

{-@ measure elements @-}
elements :: [Int] -> Set.Set Int 
elements []        = Set.empty
elements (x:xs) = Set.singleton x `Set.union` elements xs


{-@ predicate ListUnique X = (Set_emp (dups X)) @-}

{-@ type UList a = {v:[a] | (ListUnique v)}     @-}


-- * Session types

{-@ data Send tag a s = Send (SendOnce (a, Dual s)) @-}
data Send tag a s = Send (SendOnce (a, Dual s))
{-@ data Recv tag a s = Recv (RecvOnce (a, s)) @-}
data Recv tag a s = Recv (RecvOnce (a, s))
data End      = End SyncOnce


-- FIXME: invariant para el type tag? como que no sé si podría ser útil que subtipe
--
{-@ data variance Recv invariant covariant covariant @-}
{-@ data variance Send invariant contravariant covariant @-}


-- * Duality and session initiation

-- con esto ghc da stack overflow, o sea, Session (Dual s)
-- class ( Session (Dual s), Dual (Dual s) ~ s) => Session s where
class (Dual (Dual s) ~ s) => Session s where
  type Dual s = result | result -> s
  newS :: IO (s, Dual s)

instance Session s => Session (Send tag a s) where
  type Dual (Send tag a s) = Recv tag a (Dual s)
  newS = bimap Send Recv <$> new'

instance Session s => Session (Recv tag a s) where
  type Dual (Recv tag a s) = Send tag a (Dual s)
  newS = bimap Recv Send . swap <$> new'

instance Session End where
  type Dual End = End
  newS = bimap End End <$> newSync

instance Session () where
  type Dual () = ()
  newS = return ((), ())


-- * Communication primitives

{-@ assume send :: Session s => v1:Int -> Send Any {v2:Int | v1 = v2} s -> RIO<{\w1 -> true}, {\w1 b w2 -> NextWorld w1 v1 w2}> s @-}
send :: Session s => Int -> Send Any Int s -> RIO s
send = sendUnsafe


{-@ assume recv :: Recv Any Int s -> RIO<{\w -> true}, {\w1 v w2 -> NextWorld w1 (fst v) w2}> (Int, s) @-}
recv :: Recv Any Int s -> RIO (Int, s)
recv = recvUnsafe

{-@ assume sendUnsafe :: Session s => v1:Int -> Send a {v2:Int | v1 = v2} s -> RIO<{\w1 -> true}, {\w1 b w2 -> NextWorld w1 v1 w2}> s @-}
sendUnsafe :: Session s => Int -> Send a Int s -> RIO s
sendUnsafe x (Send ch_s) = do
  (here, there) <- (liftRIO newS)
  liftRIO $ send' ch_s (x, there)
  return here


{-@ assume recvUnsafe :: Recv a Int s -> RIO<{\w -> true}, {\w1 v w2 -> NextWorld w1 (fst v) w2}> (Int, s) @-}
recvUnsafe :: Recv a Int s -> RIO (Int, s)
recvUnsafe (Recv ch_r) = do
  liftRIO $ recv' ch_r

{-@ close :: End -> RIO <{\x -> true}, {\w1 b w2 -> Pure w1 w2}> () @-}
close :: End -> RIO ()
close (End s) = liftRIO $ sync s

{-@ assume connect :: (Session s) => (s -> RIO <{\w -> EmptyWorld w}> ()) -> (Dual s -> RIO <{\w -> EmptyWorld w}> a) -> IO a @-}
connect :: (Session s) => (s -> RIO ()) -> (Dual s -> RIO a) -> IO a
connect k1 k2 = do 
  (s1, s2) <- newS
  void (forkIO (gi (k1 s1)))
  gi (k2 s2)
  where gi rio = let io = rState rio $ W in fmap fst io


--
-- branching

type Select s_1 s_2 = Send Any (Either (Dual s_1) (Dual s_2)) ()
type Offer s_1 s_2 = Recv Any (Either s_1 s_2) ()


{-@ assume selectLeft :: Session s => Select s_1 s_2 -> RIO<{\w1 -> true}, {\w1 v w2 -> Pure w1 w2 }> s_1 @-}
selectLeft :: (Session s_1) => Select s_1 s_2 -> RIO s_1
selectLeft (Send s) = do 
  (here, there) <- (liftRIO newS)
  liftRIO $ send' s (Left there, ())
  return here

{-@ assume selectRight :: Session s => Select s_1 s_2 -> RIO<{\w1 -> true}, {\w1 v w2 -> Pure w1 w2}> s_2 @-}
selectRight :: (Session s_2) => Select s_1 s_2 -> RIO s_2
selectRight (Send s) = do 
  (here, there) <- (liftRIO newS)
  liftRIO $ send' s (Right there, ())
  return here

{-@ assume offerEither :: forall <p :: World -> Bool, q :: World -> a -> World -> Bool>. Offer s_1 s_2 -> (Either s_1 s_2 -> RIO<p, q> a) -> RIO<p, q> a @-}
offerEither ::  Offer s_1 s_2 -> (Either s_1 s_2 -> RIO a) -> RIO a
offerEither (Recv s) match = do 
    (e, ()) <- (liftRIO $ recv' s)
    match e

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

--  un par de helpers
--
{-@ liquidAssert :: {v:Bool | v} -> () @-}
liquidAssert :: Bool -> ()
liquidAssert b = () 

{-@ assertLastValueIs :: x:Int -> RIO<{\w -> lastVal w = x}> () @-}
assertLastValueIs :: Int -> RIO ()
assertLastValueIs _ = return ()

