module Prover where

import Control.Monad

import FirstOrder.Formula
import FirstOrder.Skolemization
import FirstOrder.Signature
import FirstOrder.Conversion
import Herbrand
import Propositional.DavisPutnamSAT
import Utils
import Alternate


removeForall :: Formula -> Formula
removeForall alpha = case alpha of
  
  Not phi         -> Not $ removeForall phi

  Or      phi psi -> Or       (removeForall phi) (removeForall psi)
  And     phi psi -> And      (removeForall phi) (removeForall psi)
  Implies phi psi -> Implies  (removeForall phi) (removeForall psi)
  Iff     phi psi -> Iff      (removeForall phi) (removeForall psi)

  Exists x phi    -> error "not a skolemized formula"
  Forall x phi    -> removeForall phi

  _               -> alpha


prover :: Formula -> Bool
prover phi = if null funcs then
    not bruteCheck

  else
    or $ map not $ toList results 
    
    where

      psi = skolemize $ Not phi
      ksi = removeForall psi

      xs = vars ksi

      signature = sig ksi

      terms :: [Term]
      terms = map fromGTerm $ herbrandUni signature

      (cts, funcs) = splitSig signature
      
      -- try all potential "and-ed" instances of `ksi` (ksi_1 /\ ksi_2 /\ ...)
      results :: Alternate Bool
      results = do
        
        k <- fromList [1..]

        termSets <- replicateM k $ replicateM (length xs) $ fromList terms

        let substs = [makeSubst xs ts | ts <- termSets]

        return $ solve substs ksi

      
      -- check whether a formula made by "and-ing" (ksi_1 /\ ksi_2 /\ ...) all 
      -- (finitely many) possible instances of `ksi`  is satisfiable
      bruteCheck :: Bool
      bruteCheck = solve substs ksi  where
        
        substs :: [Substitution]
        substs = do

          ts <- replicateM (length xs) terms

          return $ makeSubst xs ts



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
  phiInstance = foldl1 And [apply subst phi | subst <- substs]
    
  (_, assignment) = assignProps phiInstance
  propInstance = quantFreeFOToProp assignment phiInstance
  
  in satDP propInstance


