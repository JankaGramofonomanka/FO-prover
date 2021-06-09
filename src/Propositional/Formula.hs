{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances #-}

module Propositional.Formula where



import Data.List
import Utils






-- generation of fresh variable names
type VarName = String
fresh :: [VarName] -> VarName
fresh vars = head $ filter (not . (`elem` vars)) $ map (("p"++) . show) [0..]

copy = undefined
todo = undefined

-- Variable names are just strings
type PropName = String

data Formula =
      T
    | F
    | Prop PropName -- atomic formulas
    | Not Formula
    | And Formula Formula
    | Or Formula Formula
    | Implies Formula Formula
    | Iff Formula Formula
    deriving (Eq, Show)
    
p, q, r, s, t :: Formula

p = Prop "p"
q = Prop "q"
r = Prop "r"
s = Prop "s"
t = Prop "t"


infixr 8 /\, ∧
(/\) = And
(∧) = And

infixr 5 \/, ∨, ==>
(\/) = Or
(∨) = Or -- input with "\or"
(==>) = Implies

infixr 4 <==>, ⇔
(<==>) = Iff
(⇔) = Iff -- input with "\lr"




    
type Valuation = PropName -> Bool

eval :: Formula -> Valuation -> Bool
-- eval = copy -- copy from the previous lab
eval T _ = True
eval F _ = False
eval (Prop p) ρ = ρ p
eval (Not φ) ρ = not (eval φ ρ)
eval (And φ ψ) ρ = eval φ ρ && eval ψ ρ
eval (Or φ ψ) ρ = eval φ ρ || eval ψ ρ
eval (Implies φ ψ) ρ = eval φ ρ ==> eval ψ ρ where
  (==>) :: Bool -> Bool -> Bool
  a ==> b = not a || b
eval (Iff φ ψ) ρ = eval φ ρ <=> eval ψ ρ where
  (<=>) :: Bool -> Bool -> Bool
  a <=> b = a == b


variables :: Formula -> [PropName]
variables = nub . go where
  go T = []
  go F = []
  go (Prop p) = [p]
  go (Not φ) = go φ
  go (And φ ψ) = go φ ++ go ψ
  go (Or φ ψ) = go φ ++ go ψ
  go (Implies φ ψ) = go φ ++ go ψ
  go (Iff φ ψ) = go φ ++ go ψ



valuations :: [PropName] -> [Valuation]
valuations [] = [undefined]
valuations (x : xs) = concat [[update ϱ x True, update ϱ x False] | ϱ <- valuations xs]







type SATSolver = Formula -> Bool



satisfiable :: SATSolver
satisfiable φ = or [eval φ ϱ | ϱ <- valuations (variables φ)]



tautology :: Formula -> Bool
-- tautology φ = copy -- copy from the previous lab
tautology φ = not $ satisfiable $ Not φ



nnf :: Formula -> Formula
-- nnf = copy -- copy from the previous lab
nnf α = case α of
  T -> T
  F -> F
  Prop p -> Prop p
  And φ ψ -> (nnf φ) ∧ (nnf ψ)
  Or φ ψ -> (nnf φ) ∨ (nnf ψ)
  
  Not (Prop p) -> α
  Not β -> nnf $ pushNegation α
  
  -- Implies, Iff
  _ -> nnf $ disassemble α


disassemble :: Formula -> Formula
disassemble α = case α of
  Implies φ ψ -> (Not φ) ∨ ψ
  Iff φ ψ -> ((Not φ) ∨ ψ) ∧ (φ ∨ Not ψ)
  _ -> α

pushNegation :: Formula -> Formula
pushNegation (Not α) = case α of
  T -> F
  F -> T
  Prop p -> Not $ Prop p
  Not φ -> φ

  And φ ψ -> (Not φ) ∨ (Not ψ)
  Or φ ψ -> (Not φ) ∧ (Not ψ)

  -- Implies, Iff
  _ -> pushNegation $ Not $ disassemble α

pushNegation α = α







