-- Language Engineering
-- Denotational Semantics
-- CWK2p1

-- Type Definitions (Given)

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

{-

fv_aexp :: Aexp -> [Var] 
fv_bexp :: Bexp -> [Var]

subst_aexp :: Aexp -> Var -> Aexp -> Aexp
subst_bexp :: Bexp -> Var -> Aexp -> Bexp

a_val :: Aexp -> State -> Z
b_val :: Bexp -> State -> T

-}