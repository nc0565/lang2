-- Language Engineering
-- Denotational Semantics
-- CWK2p1

-- Type Definitions (Given)
import Control.Applicative
import Data.List

type Var = String
type Z = Integer
type T = Bool
type State = Var -> Z

data Aexp = N Integer
            | V Var
            | Add Aexp Aexp
            | Mult Aexp Aexp
            | Sub Aexp Aexp deriving (Show)

data Bexp = TRUE
            | FALSE
            | Eq Aexp Aexp
            | Le Aexp Aexp
            | Neg Bexp
            | And Bexp Bexp deriving (Show)

data Stm  = Ass Var Aexp
            | Skip
            | Comp Stm Stm
            | If Bexp Stm Stm
            | While Bexp Stm deriving (Show)

-- Semantic Functions (To Do)

-- Could change pattern the generalise operators

fv_aexp :: Aexp -> [Var] 
fv_aexp (N n) = []
fv_aexp (V x) = [x]
fv_aexp (Add a1 a2) = (fv_aexp a1) `union` (fv_aexp a2)
fv_aexp (Mult a1 a2) = (fv_aexp a1) `union` (fv_aexp a2)
fv_aexp (Sub a1 a2) = (fv_aexp a1) `union` (fv_aexp a2)

fv_bexp :: Bexp -> [Var]
fv_bexp TRUE  = []
fv_bexp FALSE = []
fv_bexp (Eq a1 a2)  = (fv_aexp a1) `union` (fv_aexp a2)
fv_bexp (Le a1 a2)  = (fv_aexp a1) `union` (fv_aexp a2)
fv_bexp (Neg b1)    = fv_bexp b1
fv_bexp (And b1 b2) = (fv_bexp b1) `union` (fv_bexp b2)

subst_aexp :: Aexp -> Var -> Aexp -> Aexp
subst_aexp (N n) _ _ = (N n)
subst_aexp (V v) x sub
        | v == x = sub
        | otherwise = (V v)
subst_aexp (Add  a1 a2) x sub = Add (subst_aexp a1 x sub) (subst_aexp a2 x sub)
subst_aexp (Mult a1 a2) x sub = Mult (subst_aexp a1 x sub) (subst_aexp a2 x sub)
subst_aexp (Sub  a1 a2) x sub = Sub (subst_aexp a1 x sub) (subst_aexp a2 x sub)

subst_bexp :: Bexp -> Var -> Aexp -> Bexp
subst_bexp TRUE _ _  = TRUE
subst_bexp FALSE _ _ = FALSE
subst_bexp (Eq a1 a2) x sub  = Eq (subst_aexp a1 x sub) (subst_aexp a2 x sub)
-- Check
subst_bexp (Neg b1) x sub    = Neg (subst_bexp b1 x sub)
subst_bexp (And b1 b2) x sub = And (subst_bexp b1 x sub) (subst_bexp b2 x sub)
   
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

s_ds :: Stm -> State -> State
s_ds (Ass x a1) = /s y -> update (a_val a1 s) x
        where update s z x y
                | y == x = z
                | otherwise = s y
s_ds Skip = id
s_ds (Comp st1 st2) = (s_ds st2) . (s_ds st1)
s_ds (If b1 st1 st2) = cond ((b_val b1), (s_ds st1), (s_ds st2))
s_ds (While b1 st1) = fix ff
        where ff g = cond ((b_val b1), (g . s_ds st1), id)


{- Tests
 ===================================
 let bob::State; bob _ = 4
 b_val (Neg TRUE) bob
 it = False

b_val (And TRUE TRUE) bob
it = True

b_val (Eq (N 4) (Add (N 2) (N 2))) bob
it = True

b_val ( subst_bexp (Eq (N 4) (Add (N 2) (N 2))) "x" (N 4)) bob
it = True

b_val ( subst_bexp (Eq (N 4) (Add (N 2) (N 2))) ( head ( fv_aexp (V "x"))) (N 4)) bob
it = True

fv_bexp (Eq (N 2) (V "x"))
it = ["x"]

 b_val ( subst_bexp (Eq (N 4) (Add (N 2) (N 2))) ( head ( fv_bexp (Eq (N 2) (V "x")))) (N 4)) bob
 it = True
-}
