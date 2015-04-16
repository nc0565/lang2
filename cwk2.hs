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
cond (p, st1, st2) s
        | p s = (s_ds st1) s
        | otherwise = (s_ds st2) s

fix :: (a -> a) -> a
fix f = f (fix f)
--fix f = let x = f x in x


--new :: Loc -> Loc
--lookup :: EnvV -> Store -> State
--update :: Eq a => (a->b) -> b -> a -> (a->b)
--s_ds' :: Stm -> EnvV -> Store -> Store
--d_v_ds :: DecV -> (EnvV, Store) -> (EnvV, Store)    
--d_p_ds :: DecP -> EnvV -> EnvP -> EnvP  
--s_ds :: Stm -> EnvV -> EnvP -> Store -> Store
