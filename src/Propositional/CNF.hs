{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances #-}

module Propositional.CNF where


import Data.List
import Control.Monad
import Control.Monad.State
import Test.QuickCheck
import System.IO.Unsafe


import Propositional.Formula



data Literal = Pos PropName | Neg PropName deriving (Eq, Show, Ord)

literal2var :: Literal -> PropName
literal2var (Pos p) = p
literal2var (Neg p) = p

opposite :: Literal -> Literal
opposite (Pos p) = Neg p
opposite (Neg p) = Pos p




type CNFClause = [Literal]
type CNF = [CNFClause]

cnf2formula :: CNF -> Formula
cnf2formula [] = T
cnf2formula lss = foldr1 And (map go lss) where
  go [] = F
  go ls = foldr1 Or (map go2 ls)
  go2 (Pos p) = Prop p
  go2 (Neg p) = Not (Prop p)
  
positive_literals :: CNFClause -> [PropName]
positive_literals ls = nub [p | Pos p <- ls]

negative_literals :: CNFClause -> [PropName]
negative_literals ls = nub [p | Neg p <- ls]

literals :: [Literal] -> [PropName]
literals ls = nub $ positive_literals ls ++ negative_literals ls




cnf :: Formula -> CNF
cnf = go . nnf where
  go T = []
  go F = [[]]
  go (Prop p) = [[Pos p]]
  go (Not (Prop p)) = [[Neg p]]
  go (φ `And` ψ) = go φ ++ go ψ
  go (φ `Or` ψ) = distribute (go φ) (go ψ)
  
-- find all ways of joining the lists (c.f. example below)
distribute :: [[a]] -> [[a]] -> [[a]]
distribute xss yss = go xss yss yss where
  go [] _ _ = []
  go (_:xss) yss [] = go xss yss yss
  go (xs:xss) yss (ys:yss') = (xs ++ ys) : go (xs:xss) yss yss'

prop_distribute :: Bool
prop_distribute = distribute [[1, 2], [3, 4]] [[5, 6], [7]] == [[1, 2, 5, 6], [1, 2, 7], [3, 4, 5, 6], [3, 4, 7]]





test_cnf :: Formula -> Bool
test_cnf φ = tautology $ φ ⇔ (cnf2formula (cnf φ))

--quickCheckWith (stdArgs {maxSize = 18}) test_cnf



equi_satisfiable :: Formula -> Formula -> Bool
equi_satisfiable φ ψ = satisfiable φ == satisfiable ψ




ecnf :: Formula -> CNF
ecnf α = evalState convert initState where

  vars = variables α
  p0 = fresh vars
  initState = (vars ++ [p0], [(p0, α)], [Prop p0])




cnfAnd :: CNF -> CNF -> CNF
cnfAnd = (++)

trivial :: Formula -> Bool
trivial α = case α of
  T -> True
  F -> True
  
  Prop p -> True
  Not (Prop p) -> True
  
  _-> False

type PropDef = (PropName, Formula)
type ConverterState = ([PropName], [PropDef], [Formula])


getPropDefs :: State ConverterState [PropDef]
getPropDefs = do
  (_, propDefs, _) <- get
  return propDefs

getSimpleFromulas :: State ConverterState [Formula]
getSimpleFromulas = do
  (_, _, simpleFormulas) <- get
  return simpleFormulas


freshProp :: State ConverterState PropName
freshProp = do
  (vars, propDefs, simpleFormulas) <- get
  let prop = fresh vars
  put (vars ++ [prop], propDefs, simpleFormulas)

  return prop

addPropDefs :: [PropDef] -> State ConverterState ()
addPropDefs newPropDefs = do
  (vars, propDefs, simpleFormulas) <- get
  put (vars, propDefs ++ newPropDefs, simpleFormulas)

addSimpleFormula :: Formula -> State ConverterState ()
addSimpleFormula α = do
  (vars, propDefs, simpleFormulas) <- get
  put (vars, propDefs, simpleFormulas ++ [α])

popDef :: State ConverterState PropDef
popDef = do
  (vars, propDefs, simpleFormulas) <- get
  put (vars, tail propDefs, simpleFormulas)

  return $ head propDefs



convert :: State ConverterState CNF
convert = do

  loop

  simpleFormulas <- getSimpleFromulas

  return $ foldl cnfAnd [] $ map cnf simpleFormulas


  where

    loop :: State ConverterState ()
    loop = do
      propDefs <- getPropDefs

      case propDefs of
        [] -> return ()
        
        _ -> do

          (prop, α) <- popDef
          
          simpleAlpha <- simplify α
          addSimpleFormula $ Prop prop <==> simpleAlpha
          loop






simplify :: Formula -> State ConverterState Formula
simplify α = case α of

  Not φ       -> do
    simplePhi <- simplify φ
    return $ Not simplePhi
    
  And φ ψ     -> simplifyBinary And φ ψ
  Or φ ψ      -> simplifyBinary Or φ ψ
  Implies φ ψ -> simplifyBinary Implies φ ψ
  Iff φ ψ     -> simplifyBinary Iff φ ψ
  
  _           -> return α


simplifyBinary :: (Formula -> Formula -> Formula) -> Formula -> Formula -> 
  State ConverterState Formula
simplifyBinary op φ ψ = if trivial φ && trivial ψ then do
    
      return $ φ `op` ψ

    else if trivial φ then do

      prop <- freshProp
      let propDef = (prop, ψ)
      addPropDefs [propDef]
      
      return $ φ `op` Prop prop

    else if trivial ψ then do

      prop <- freshProp
      let propDef = (prop, φ)
      addPropDefs [propDef]

      return $ Prop prop `op` ψ


    else do

      propPhi <- freshProp
      let propPhiDef = (propPhi, φ)
      propPsi <- freshProp
      let propPsiDef = (propPsi, ψ)
      addPropDefs [propPhiDef, propPsiDef]
      return $ Prop propPhi `op` Prop propPsi




prop_ecnf :: Formula -> Bool
prop_ecnf phi = equi_satisfiable phi (cnf2formula $ ecnf phi)

--quickCheckWith (stdArgs {maxSize = 18}) prop_ecnf
--quickCheck prop_ecnf


