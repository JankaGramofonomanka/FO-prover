{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances #-}

module Propositional.DavisPutnamSAT where


import Data.List


import Propositional.Formula
import Propositional.CNF








remove_tautologies :: CNF -> CNF
remove_tautologies clauses = foldl foldF [] clauses where
  foldF acc clause = if taut clause then acc else acc ++ [clause]
  
  taut :: CNFClause -> Bool
  taut [] = False
  taut (Pos p : literals) = elem (Neg p) literals || taut literals
  taut (Neg p : literals) = elem (Pos p) literals || taut literals








one_literal :: CNF -> CNF
one_literal α = case getSingleLiteral α of
  Nothing -> α
  Just lit -> one_literal $ remove_clauses lit α

getSingleLiteral :: CNF -> Maybe Literal
getSingleLiteral α = foldr foldF Nothing α where
  foldF :: CNFClause -> Maybe Literal -> Maybe Literal
  foldF _ (Just lit) = Just lit
  foldF clause Nothing = case clause of
    [lit] -> Just lit
    _ -> Nothing


remove_clauses :: Literal -> CNF -> CNF
remove_clauses literal β = foldl foldF [] β where
  
    foldF :: CNF -> CNFClause -> CNF
    foldF acc clause = if elem literal clause then 
        acc
      else 
        acc ++ [filter (/= (opposite literal)) clause]
    
  











affirmative_negative :: CNF -> CNF
affirmative_negative α = rem_clauses allLits α where
  allLits = (getLiterals α)

  rem_clauses :: [Literal] -> CNF -> CNF
  rem_clauses lits β = case lits of
    [] -> β
    (lit : otherLits) -> if elem (opposite lit) allLits then
        rem_clauses otherLits β
      else let
          γ = remClausesWLit lit β
        in rem_clauses otherLits γ
  
  remClausesWLit :: Literal -> CNF -> CNF
  remClausesWLit lit β = foldl foldF [] β where
    foldF acc clause = if elem lit clause then acc else acc ++ [clause]
  
  getLiterals :: CNF -> [Literal]
  getLiterals β = nub $ foldl (++) [] β
    










resolution :: CNF -> CNF
resolution α = let
    p = getLiteral α
    
    -- α = β ∧ (p ∨ φ) ∧ (¬p ∨ ψ)
    (β, φ, ψ) = segregate p α
    
  
  in β `cnfAnd` (φ `cnfOr` ψ)

cnfOr :: CNF -> CNF -> CNF
φ `cnfOr` ψ = foldl cnfAnd [] $ map (\clause -> map (clause `clauseOr`) φ) ψ

clauseOr :: CNFClause -> CNFClause -> CNFClause
clauseOr = (++)

getLiteral :: CNF -> Literal
getLiteral (clause : clauses) = case clause of
  [] -> getLiteral clauses
  lit : lits -> lit

segregate :: Literal -> CNF -> (CNF, CNF, CNF)
segregate lit α = foldl foldF ([], [], []) $ map nub α where
  foldF (accBeta, accPhi, accPsi) clause = if elem lit clause then
      (accBeta, accPhi ++ [delete lit clause], accPsi)
    else if elem (opposite lit) clause then
      (accBeta, accPhi, accPsi ++ [delete (opposite lit) clause])
     else 
      (accBeta ++ [clause], accPhi, accPsi)
    








satDP :: SATSolver
satDP α = satCNF $ ecnf α where
  satCNF cnfForm = case cnfForm of
    [] -> True
    β -> if elem [] β then False else let
        post3 = remove_tautologies β
        post4 = one_literal post3
        post5 = affirmative_negative post4
    
      in satCNF $ resolution post5
    



