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
fv_bexp (Eq a1 a2) = (fv_aexp a1) `union` (fv_aexp a2)
fv_bexp (Le a1 a2) = (fv_aexp a1) `union` (fv_aexp a2)
fv_bexp (Neg b1) = fv_bexp b1
fv_bexp (And b1 b2) = (fv_bexp b1) `union` (fv_bexp b2)


--subst_aexp :: Aexp -> Var -> Aexp -> Aexp
--subst_bexp :: Bexp -> Var -> Aexp -> Bexp
    
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
