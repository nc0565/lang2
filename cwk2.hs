-- Language Engineering
-- Denotational Semantics
-- CWK2

import Prelude hiding (lookup)

-- Type Definitions (Given)

data Aexp = N Integer | V Var | Add Aexp Aexp | Mult Aexp Aexp | Sub Aexp Aexp
data Bexp = TRUE | FALSE | Eq Aexp Aexp | Le Aexp Aexp | Neg Bexp | And Bexp Bexp
data Stm  = Ass Var Aexp | Skip | Comp Stm Stm | If Bexp Stm Stm | While Bexp Stm | Block DecV DecP Stm | Call Pname

type Var = String
type Pname = String
type DecV = [(Var,Aexp)]
type DecP = [(Pname,Stm)]

type Z = Integer
type T = Bool
type State = Var -> Z
type Loc = Z
type Store = Loc -> Z
type EnvV = Var -> Loc
type EnvP = Pname -> Store -> Store

next = 0

s::Stm
s = Comp (Ass "x" (N 7)) (inner)
        where inner = Block [("x", (N 7))] [("p", (Ass "x" (N 0)))] (Comp (Ass "x" (N 5)) (Call "p"))

{-begin
    var x:=7;
    proc p is x:=0;
    begin
        var x:=5;
        call p
    end
end-}
-- Semantic Functions (To Do)

a_val :: Aexp -> State -> Z
a_val (N i) s = i
a_val (V x) s = s x
a_val (Add  a1 a2) s = (a_val a1 s) + (a_val a2 s)
a_val (Mult a1 a2) s = (a_val a1 s) * (a_val a2 s)
a_val (Sub  a1 a2) s = (a_val a1 s) - (a_val a2 s)

b_val :: Bexp -> State -> T
b_val TRUE s = True
b_val FALSE s = False
b_val (Eq a1 a2) s
        | (a_val a1 s) == (a_val a2 s) = True
        | otherwise = False
b_val (Le a1 a2) s
        | (a_val a1 s) <= (a_val a2 s) = True
        | otherwise = False
        -- (a1)s > (a2 s)
b_val (Neg b1) s = not (b_val b1 s)
b_val (And b1 b2) s = (b_val b1 s) && (b_val b2 s)
--b_val (And b1 b2) s = liftA2 (&&) (b_val b1 s) (b_val b2 s)

cond :: (a->T, a->a, a->a) -> (a->a)
cond (p, st1, st2) envv
        | p envv = st1 envv
        | otherwise = st2 envv

fix :: (a -> a) -> a
fix f = f (fix f)
--fix f = let x = f x in x

new :: Loc -> Loc
new = succ

lookup :: EnvV -> Store -> State
--lookup :: ("x"->4) -> (4->6) -> State
lookup envv sto = sto . envv

-- ******************************
-- Only works with Eq b=>
-- ******************************
update :: Eq a => Eq b => (a->b) -> b -> a -> (a->b)
update f val x
        | (f x) == val  = f
        | otherwise = update'
                where update' y
                        | y == x = val
                        | otherwise = f y

s_ds' :: Stm -> EnvV -> Store -> Store
--s_ds' :: Stm -> (Var -> Loc) -> (Loc -> Z) -> (Loc -> Z)
s_ds' (Ass x a1) envv = \sto -> update sto (a_val a1 (lookup envv sto)) (envv x)
s_ds' Skip envv = id
s_ds' (Comp st1 st2) envv = (s_ds' st2 envv) . (s_ds' st1 envv)
s_ds' (If b1 st1 st2) envv = cond ((b_val b1 . lookup envv), (s_ds' st1 envv), (s_ds' st2 envv))
s_ds' (While b1 st1) envv = fix ff
        where ff g = cond ((b_val b1 . lookup envv), (g . (s_ds' st1 envv)), id)

--d_v_ds :: DecV -> (EnvV, Store) -> (EnvV, Store)    
--d_p_ds :: DecP -> EnvV -> EnvP -> EnvP  
--s_ds :: Stm -> EnvV -> EnvP -> Store -> Store


evv::Var->Loc
evv "x" = 1
evv "h" = 4

st::Loc->Z
st 1 = 5
st 2 = 6
st 4  = 10


{-Tests
=====================================
let test = s_ds' (Comp Skip Skip) bob
let {bob::Var->Loc;bob "x" = 4}
let {tim::Loc->Z;tim 4 = 6}

(test tim) 4
it = 6

let {pred::Store->T;pred p = True}
let{evv::Var->Loc;evv x = 2}
let {st::Loc->Z;st 2 = 6;st _  =4 }
let test = cond (pred, (s_ds' Skip evv), (s_ds' Skip evv)) $ st

test 2
6
it :: Z

let test = cond (pred, (s_ds' Skip evv), (s_ds' Skip evv)) st . evv
test "x"
6
it :: Z

cond ((b_val b1 . (lookup envv)), (s_ds' st1 envv), (s_ds' st2 envv))

let test = lookup evv (s_ds'  (Ass "h" (N 7)) evv st)

(lookup evv st) "h"
10
test "h"
7
test "x"
5
test "t"
undefined   
-}