{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}

{-# LANGUAGE NamedFieldPuns                   #-}

module Env where

import Prelude hiding (lookup)
import qualified Data.Set as Set

-- * Lang

type Var  = String
{-@ type Var = String @-}

{-@ data Expr = Number Int | Var Var | Add Expr Expr | Equal Expr Expr | Not Expr | And Expr Expr @-}
data Expr = Number Int | Var Var | Add Expr Expr | Equal Expr Expr | Not Expr | And Expr Expr deriving Show

{-@ measure val @-}
val              :: Expr -> Bool
val (Number _)    = True
val _             = False

{-@ type ClosedExpr G = {v:Expr | Subset (free v) (keys G)} @-}
{-@ type Val = {v:Expr | val v} @-}

{-@ measure free @-}
free               :: Expr -> Set.Set Var
free (Number _)     = Set.empty
free (Var x)       = Set.singleton x
free (Add e1 e2)   = free e1 `Set.union` free e2
free (Equal e1 e2) = free e1 `Set.union` free e2
free (And e1 e2)   = free e1 `Set.union` free e2
free (Not e)       = free e

{-@ measure number @-}
number :: Expr -> Bool
number (Number _) = True
number _          = False

-- función de evaluación (dado un environment/context)

{-@ reflect eval @-}
{-@ eval :: e: Env -> ClosedExpr e -> Val @-}
eval :: Env -> Expr -> Expr
eval env (Add e1 e2) = add (eval env e1) (eval env e2)
eval env (And e1 e2) = evalAnd (eval env e1) (eval env e2)
eval env (Equal e1 e2) = equal (eval env e1) (eval env e2)
eval env (Not e1) = neg (eval env e1)
eval env (Number n) = Number n
eval env (Var v) = lookup v env 

{-@ reflect add @-}
{-@ add :: Val -> Val -> Val @-}
add :: Expr -> Expr -> Expr
add (Number a) (Number b) = Number (a + b)

{-@ reflect equal @-}
{-@ equal :: Val -> Val -> Val @-}
equal :: Expr -> Expr -> Expr
equal (Number a) (Number b) = if a == b then Number 1 else Number 0

{-@ reflect neg @-}
{-@ neg :: Val -> Val @-}
neg :: Expr -> Expr
neg (Number 0)  = Number 1
neg (Number _)  = Number 0

{-@ reflect evalAnd @-}
{-@ evalAnd :: Val -> Val -> Val @-}
evalAnd :: Expr -> Expr -> Expr
evalAnd (Number a) (Number b) = Number (collapse (a * b))

{-@ reflect collapse @-}
{-@ collapse :: j:Int -> {i: Int | i == 0 || i == 1 } @-}
collapse :: Int -> Int
collapse i = if i == 0 then 0 else 1

{-@ reflect equalAdd @-}
equalAdd :: Expr
equalAdd = Equal (Add (Var "x") (Var "y")) (Number 3)

testEqualAdd = assert (toBoolean (eval (insert "x" (Number 2) (insert "y" (Number 1) empty)) equalAdd))
testAndPos = assert (toBoolean (eval empty (And (Number 1) (Number 2))))
testAndNeg = assert (not (toBoolean (eval empty (And (Number 1) (Number 0)))))
testAny = assert (toBoolean (eval empty any_c))

{-@ reflect toBoolean @-}
{-@ toBoolean :: Val -> Bool @-}
toBoolean :: Expr -> Bool
toBoolean (Number 0) = False
toBoolean (Number _) = True

{-@ reflect any_c @-}
any_c :: Expr 
any_c = Equal (Number 1) (Number 1)

{-@ reflect or_c @-}
or_c :: Expr -> Expr -> Expr
or_c a b = Not (And (Not a) (Not b))

{-@ reflect and_c @-}
and_c :: Expr -> Expr -> Expr
and_c a b = And a b

-- environment/context (map) based on a list

data Env = Cons Var Expr Env | Nil deriving Show

{-@ data Env = Cons Var Val Env | Nil @-}

{-@ reflect insert @-}
{-@ insert :: v:Var -> e:Val -> m:Env -> {n: Env | AddKey v m n} @-}
insert :: Var -> Expr -> Env -> Env
insert = Cons

{-@ reflect lookup @-}
{-@ lookup :: v:Var -> { m: Env | HasKey v m } -> Val @-}
lookup :: Var -> Env -> Expr
lookup k (Cons x v xs) = if k == x then v else lookup k xs

{-@ reflect empty @-}
{-@ empty :: {m: Env | Empty (keys m) } @-}
empty :: Env
empty = Nil

{-@ measure keys @-}
{-@ keys :: Env -> Set Var @-}
keys :: Env -> Set.Set Var
keys Nil = Set.empty
keys (Cons k v xs) = Set.singleton k `Set.union` keys xs

{-@ predicate In X Xs      = Set_mem X Xs               @-}
{-@ predicate Subset X Y   = Set_sub X Y                @-}
{-@ predicate Empty  X     = Set_emp X                  @-}
{-@ predicate Union X Y Z  = X = Set_cup Y Z            @-}
{-@ predicate Union1 X Y Z = Union X (Set_sng Y) Z      @-}
{-@ predicate HasKey K M   = In K (keys M)              @-}
{-@ predicate AddKey K M N = Union1 (keys N) K (keys M) @-}
{-@ predicate Disjoint K M = Set_emp (Set_cap (keys K) (keys M)) @-}

{-@ assert :: {b: Bool | b } -> () @-}
assert :: Bool -> ()
assert False = error "unreachable"
assert True = ()

-- Session

data Session = Session { env :: Env, constraint :: Expr } deriving Show

{-@ measure env @-}
{-@ measure constraint @-}

{-@ reflect send @-}
send :: Session -> Var -> Int -> Session
send Session { env, constraint } v i = let newEnv = insert v (Number i) env in 
    Session { env = newEnv, constraint = constraint }

{-@ reflect recv @-}
recv :: Session -> Expr -> Session
recv Session { env, constraint } e = let newConstraint = constraint `and_c` e in 
    Session { env = env, constraint = newConstraint }

{-@ reflect par @-}
{-@ par :: s1:Session -> { s2:Session | Disjoint (env s1) (env s2) } -> Session @-}
par s1 s2 = 
    let newEnv = env s1 `joinEnv` env s2 in 
    let newConstraint = (constraint s1) `and_c` (constraint s2) in 
    Session { env = newEnv, constraint = newConstraint }

{-@ reflect joinEnv @-}
-- TODO: poner la poscondición, pero no me está funcionando decir que e3 es la union
{-@ joinEnv :: e1:Env -> { e2:Env | Disjoint e1 e2 } -> e3:Env @-}
joinEnv (Cons xk xv xs) e2 = Cons xk xv (joinEnv xs e2)
joinEnv Nil e2 = e2 

{-@ reflect new @-}
{-@ new :: {s:Session | Empty (keys (env s)) } @-}
new :: Session
new = Session { env = empty, constraint = any_c }

{-@ reflect incrClient @-}
incrClient :: Session
incrClient = 
    let s1 = new in
    let s2 = send s1 "x" 2 in
    recv s2 (Equal (Add (Var "x") (Number 1)) (Var "y"))

{-@ reflect incrServer @-}
incrServer :: Session
incrServer = 
    let s1 = new in
    let s2 = recv s1 any_c in
    send s2 "y" 3

{-@ reflect incrSession @-}
incrSession = incrClient `par` incrServer

{-@ reflect evalSession @-}
{-@ evalSession :: {s: Session | Subset (free (constraint s)) (keys (env s)) } -> Bool @-}
evalSession s = toBoolean (eval (env s) (constraint s))

testIncrSession = assert (evalSession incrSession)