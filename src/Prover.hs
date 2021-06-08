module Prover where

import Control.Monad

import FirstOrder.Formula
import FirstOrder.Skolemization
import FirstOrder.Signature
import FirstOrder.Conversion
import Herbrand
import Propositional.DavisPutnamSAT
import Utils


removeForall :: Formula -> Formula
removeForall alpha = case alpha of
  
  Not phi         -> removeForall phi

  Or      phi psi -> Or       (removeForall phi) (removeForall psi)
  And     phi psi -> And      (removeForall phi) (removeForall psi)
  Implies phi psi -> Implies  (removeForall phi) (removeForall psi)
  Iff     phi psi -> Iff      (removeForall phi) (removeForall psi)

  Exists x phi    -> error "not a skolemized formula"
  Forall x phi    -> removeForall phi

  _               -> alpha


prover :: Formula -> Bool
prover phi = or $ map not results where

    psi = skolemize $ Not phi
    ksi = removeForall psi

    xs = vars ksi

    signature = sig ksi

    terms = map fromGTerm $ herbrandUni signature

    (cts, funcs) = splitSig signature

    ks = if null funcs then [0..(length terms)] else [0..]
    
    results :: [Bool]
    results = do
      
      k <- ks

      termSets <- replicateM k $ replicateM (length xs) terms

      let substs = [makeSubst xs ts | ts <- termSets]

      return $ solve substs ksi



makeSubst :: [VarName] -> [Term] -> Substitution
makeSubst xs ts = foldr foldF (const $ error "undefined subst") $ zip xs ts
  where
    foldF (x, t) subst = update subst x t 



solve1 :: Substitution -> Formula -> Bool
solve1 subst phi = let
  groundedPhi = apply subst phi
  (_, assignment) = assignProps groundedPhi
  propFormula = quantFreeFOToProp assignment groundedPhi

  in satDP propFormula


solve :: [Substitution] -> Formula -> Bool
solve substs phi = let
  phiInstance = foldl And T [apply subst phi | subst <- substs]
  
  (_, assignment) = assignProps phiInstance
  propInstance = quantFreeFOToProp assignment phiInstance

  in satDP propInstance


