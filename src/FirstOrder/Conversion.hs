module FirstOrder.Conversion where

import Data.List
import Control.Monad.State.Strict

import qualified FirstOrder.Formula as FO
import qualified Propositional.Formula as Prop
import Utils


data Atomic = Atomic FO.RelName [FO.Term] deriving (Eq, Show)

atomicToFOFormula :: Atomic -> FO.Formula
atomicToFOFormula (Atomic rel terms) = FO.Rel rel terms


foFormulaToAtomic :: FO.Formula -> Atomic
foFormulaToAtomic (FO.Rel rel terms) = Atomic rel terms
foFormulaToAtomic _ = error "not an atomic formula"


allAtomics :: FO.Formula -> [Atomic]
allAtomics FO.F                  = []
allAtomics FO.T                  = []

allAtomics (FO.Rel r ts)         = [Atomic r ts]
allAtomics (FO.Not phi)          = allAtomics phi

allAtomics (FO.Or phi psi)       = nub $ allAtomics phi ++ allAtomics psi
allAtomics (FO.And phi psi)      = nub $ allAtomics phi ++ allAtomics psi
allAtomics (FO.Implies phi psi)  = nub $ allAtomics phi ++ allAtomics psi
allAtomics (FO.Iff phi psi)      = nub $ allAtomics phi ++ allAtomics psi

allAtomics (FO.Exists x phi)     = allAtomics phi
allAtomics (FO.Forall x phi)     = allAtomics phi



type Bijection a b = (a -> b, b -> a)

-- Prop-Atomic - Correspondance
type PAC = Bijection Prop.PropName Atomic


assignProps :: FO.Formula -> PAC
assignProps phi = evalState (go phi initCorresp) 0 where
  initCorresp = (const err, const err)
  err = error "undefined prop / atomic"

  go :: FO.Formula -> PAC ->  State Int PAC
  go alpha cor = case alpha of

    FO.T                  -> return cor
    FO.F                  -> return cor

    (FO.Rel r ts)         -> goAtomic (Atomic r ts) cor
    (FO.Not phi)          -> go phi cor

    (FO.Or phi psi)       -> go2 phi psi cor
    (FO.And phi psi)      -> go2 phi psi cor
    (FO.Implies phi psi)  -> go2 phi psi cor
    (FO.Iff phi psi)      -> go2 phi psi cor

    (FO.Exists x phi)     -> go phi cor
    (FO.Forall x phi)     -> go phi cor

  go2 :: FO.Formula -> FO.Formula -> PAC -> State Int PAC

  go2 phi psi cor = do
    cor1 <- go phi cor
    go psi cor1

  goAtomic :: Atomic -> PAC -> State Int PAC
  
  goAtomic a (f, g) = do
    p <- newProp
    return (update f p a, update g a p)


  newProp :: State Int Prop.PropName
  newProp = do
    i <- get
    modify (+1)
    return $ "p" ++ show i
    

quantFreeFOToProp :: (Atomic -> Prop.PropName) -> FO.Formula -> Prop.Formula
quantFreeFOToProp propAss = go where

  go :: FO.Formula -> Prop.Formula
  go alpha = case alpha of

    FO.T                  -> Prop.T
    FO.F                  -> Prop.F

    (FO.Rel r ts)         -> Prop.Prop $ propAss $ Atomic r ts
    (FO.Not phi)          -> Prop.Not $ go phi

    (FO.Or      phi psi)  -> Prop.Or      (go phi) (go psi)
    (FO.And     phi psi)  -> Prop.And     (go phi) (go psi)
    (FO.Implies phi psi)  -> Prop.Implies (go phi) (go psi)
    (FO.Iff     phi psi)  -> Prop.Iff     (go phi) (go psi)

    (FO.Exists x phi)     -> error "formula is not quantifier free"
    (FO.Forall x phi)     -> error "formula is not quantifier free"

propToFO :: (Prop.PropName -> Atomic) -> Prop.Formula -> FO.Formula
propToFO atomicAss = go where

  go :: Prop.Formula -> FO.Formula
  go alpha = case alpha of
    Prop.T                -> FO.T
    Prop.F                -> FO.F
    Prop.Prop p           -> atomicToFOFormula $ atomicAss p
    Prop.Not      phi     -> FO.Not     (go phi)
    Prop.And      phi psi -> FO.And     (go phi) (go psi)
    Prop.Or       phi psi -> FO.Or      (go phi) (go psi)
    Prop.Implies  phi psi -> FO.Implies (go phi) (go psi)
    Prop.Iff      phi psi -> FO.Iff     (go phi) (go psi)