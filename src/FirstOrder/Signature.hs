module FirstOrder.Signature where

import Data.List
import Data.Ord
import FirstOrder.Formula
import Propositional.Formula (fresh)

type Arity = Int
type Signature = [(FunName, Arity)]


sigT :: Term -> Signature
sigT (Var _) = []
sigT (Fun f ts) = nub $ (f, length ts) : concatMap sigT ts

sig :: Formula -> Signature
sig T = []
sig F = []
sig (Rel r ts) = concatMap sigT ts
sig (Not phi) = sig phi
sig (And phi psi) = nub $ sig phi ++ sig psi
sig (Or phi psi) = nub $ sig phi ++ sig psi
sig (Implies phi psi) = nub $ sig phi ++ sig psi
sig (Iff phi psi) = nub $ sig phi ++ sig psi
sig (Exists _ phi) = sig phi
sig (Forall _ phi) = sig phi


ordSig :: Formula -> Signature
ordSig phi = sortBy (comparing snd) $ sig phi


splitSig :: Signature -> ([FunName], Signature)
splitSig sig = (map fst cSig, fSig) where
  (cSig, fSig) = splitBy (\t -> snd t == 0) sig

  splitBy pred = foldr f ([], []) where
    f x (yes, no) = if pred x then (x : yes, no) else (yes, x : no)
  

constants :: Signature -> [FunName]
constants sig = map fst $ filter (\t -> snd t == 0) sig




freshFunName :: Signature -> FunName
freshFunName sig = fresh $ map fst sig








