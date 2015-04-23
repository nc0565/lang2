-- Language Engineering
-- Denotational Semantics
-- CWK2

-- Note that expressions using the fac procedure should provide the EnvV [("x", (N x)), ("y",(N 1))], where x is the input.

import Prelude hiding (lookup)

-- Type Definitions (Given)

data Aexp = N Integer | V Var | Add Aexp Aexp | Mult Aexp Aexp | Sub Aexp Aexp{- deriving Show-}
data Bexp = TRUE | FALSE | Eq Aexp Aexp | Le Aexp Aexp | Neg Bexp | And Bexp Bexp{- deriving Show-}
data Stm  = Ass Var Aexp | Skip | Comp Stm Stm | If Bexp Stm Stm | While Bexp Stm | Block DecV DecP Stm
        {-| Block DecV Stm -}| Call Pname{- deriving Show-}

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
s = Block [("x", (N 7))] [("p", (Ass "x" (N 0)))] (Comp (Ass "x" (N 7)) (Block [("x", (N 5))] [{-("p", (Ass "x" (N 0)))-}] (Call "p")))

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
update :: Eq a =>{- Eq b =>-} (a->b) -> b -> a -> (a->b)
update f val x
        {-| (f x) == val  = f
        | otherwise-} = update'
                where update' y
                        | y == x = val
                        | otherwise = f y

s_ds' :: Stm -> EnvV -> Store -> Store
s_ds' (Ass x a1) envv = \sto -> update sto (a_val a1 (lookup envv sto)) (envv x)
s_ds' Skip envv = id
s_ds' (Comp st1 st2) envv = (s_ds' st2 envv) . (s_ds' st1 envv)
s_ds' (If b1 st1 st2) envv = cond ((b_val b1 . lookup envv), (s_ds' st1 envv), (s_ds' st2 envv))
s_ds' (While b1 st1) envv = fix ff where
        ff g = cond ((b_val b1 . lookup envv), (g . (s_ds' st1 envv)), id)
--s_ds' (Block dv st1) envv = \sto -> s_ds' st1' envv' sto' where 
        --d_v_ds dv (envv, sto) = (envv', sto')

--check if second arg should be PA?
d_v_ds :: DecV -> (EnvV, Store) -> (EnvV, Store)    
d_v_ds ((x, a1):dv') (envv, sto) = d_v_ds dv'((update envv l x), (update (update sto v l) (new l) next)) where
        l = sto next
        v = (a_val a1 (lookup envv sto))
d_v_ds [] (envv, sto) = {-id-} (envv, sto)

{-d_p_ds :: DecP -> EnvV -> EnvP -> EnvP
d_p_ds ((pn, st1):dp') envv envp = d_p_ds dp' envv (update envp g pn) where
        g = s_ds st1 envv envp
d_p_ds [] envv envp = {-id-} envp-}

d_p_ds :: DecP -> EnvV -> EnvP -> EnvP
d_p_ds ((pn, st1):dp') envv envp = d_p_ds dp' envv (update envp (fix ff) pn) where
        ff g = s_ds st1 envv (update envp g pn)
d_p_ds [] envv envp = {-id-} envp

s_ds :: Stm -> EnvV -> EnvP -> Store -> Store
s_ds (Ass x a1) envv envp = \sto -> update sto (a_val a1 (lookup envv sto)) (envv x)
s_ds Skip envv envp = id
s_ds (Comp st1 st2) envv envp = (s_ds st2 envv envp) . (s_ds st1 envv envp)
s_ds (If b1 st1 st2) envv envp = cond ((b_val b1 . lookup envv), (s_ds st1 envv envp), (s_ds st2 envv envp))
s_ds (While b1 st1) envv envp = fix ff where
        ff g = cond ((b_val b1 . lookup envv), (g . (s_ds st1 envv envp)), id)
s_ds (Block dv dp st1) envv envp = \sto -> s_ds st1 (envv' sto) (envp' sto) (sto' sto) where
        f s = d_v_ds dv (envv, s)
        envv' s = fst (f s)
        envp' = \sto -> d_p_ds dp (envv' sto) envp
        sto' s = snd (f s)
s_ds (Call pn ) envv envp = envp pn

t :: Store
t 0 = 1

-- After evaluation t next is the next contigous free location, so (t next)-1 = n.
countDecVars :: Stm -> Int
countDecVars st1 = (fromInteger ((s_ds st1 undefined undefined  t) next)) - 1

n :: Int
n = countDecVars s

f::DecP
f = [("fac",
    (Block [("z", (V "x"    ))] []
        (If (Eq (V "x") (N 1))
            Skip    
            (Comp 
                (Ass "x" 
                    (Sub (V "x") (N 1))) 
                (Comp 
                    (Call "fac") 
                    (Ass "y" 
                        (Mult (V "z") (V "y")) {-undefined undefined-})) {-undefined undefined-}) {-undefined undefined-})))]

{-
proc fac is begin
    var z:=x;
    if
        x=1
    then
        skip
    else
        (x:= x - 1;
        call fac;
        y:=z*y)
end
-}

--Test f, from Q.m, with the input x=5.
testM = (s_ds (Block [("x", (N 5)), ("y",(N 1))] f (Call "fac")) undefined undefined t) ((fst (d_v_ds [("x", (N 5)), ("y",(N 1))] (undefined , t))) "y")

--Testing
--evv::Var->Loc
--evv x = next

--st::Loc->Z
--st 0 = 1 -- Very importan for Testing


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

let bob = d_v_ds [("a",(N 8))] (evv, st)
(fst bob) "a"
1
(snd bob) 1
8

let sto = (snd (d_v_ds [("x", (N 5)), ("y",(N 1))] (undefined , t)))
let evv = (fst (d_v_ds [("x", (N 5)), ("y",(N 1))] (undefined , t)))
let evp = ((d_p_ds [("p", (Ass "x" (N 8)))] evv  undefined ) )


(s_ds Skip evv evp sto) 1
5
(s_ds (Call "p") evv evp sto) 1
8

let evp = ((d_p_ds [("p", (snd (head f)))] evv  undefined ) )

(s_ds (Ass "x" (N 7)) evv evp sto) 1
7
(s_ds (Block [] [] (Ass "x" (N 7))) evv evp sto) 1
7
(s_ds (Block [] [("p", (Comp (Ass "y" (N 22)) (Ass "x" (N 5))))] (Call "p")) evv evp sto) 1
5
(s_ds (Block [] [("p", (Comp (Ass "y" (N 22)) (Ass "x" (V "y"))))] (Call "p")) evv evp sto) 1
22
(s_ds (Block [] f (Ass "x" (N 6))) evv evp sto) 1
6

(s_ds (Block [] f (Call "fac")) evv evp sto) (evv "x")
1
So
(s_ds (Block [] f (Call "fac")) evv evp sto) (evv "y")
120
-}