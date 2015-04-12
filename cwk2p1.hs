-- Language Engineering
-- Denotational Semantics
-- CWK2p1

-- Type Definitions (Given)
import Control.Applicative

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



--fv_aexp :: Aexp -> [Var] 
--fv_bexp :: Bexp -> [Var]

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
