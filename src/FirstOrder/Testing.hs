{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances #-}

module FirstOrder.Testing where


import Control.Monad
import Test.QuickCheck hiding (Fun, (===))

import FirstOrder.Formula
import FirstOrder.Skolemization
import FirstOrder.Conversion
import qualified Propositional.Formula as Prop
import qualified Propositional.Testing as PropTest
import Utils

-- Formula --------------------------------------------------------------------
instance {-# OVERLAPPING #-} Arbitrary VarName where
  arbitrary = elements ["x", "y", "z", "t"]



instance Arbitrary Term where
  arbitrary = resize 8 $ sized f where
    f size | size == 0 || size == 1 = do x <- arbitrary
                                         return $ Var x
           | otherwise = frequency [ (1, go sizes) | sizes <- catalan size]
              where go sizes = do ts <- sequence $ map f sizes
                                  return $ Fun "f" ts

instance Arbitrary Formula where
  arbitrary = resize 30 $ sized f where
    f 0 = do ts <- arbitrary
             return $ Rel "R" ts
    f size = frequency [
      (1, liftM Not (f (size - 1))),
      (4, do
        size' <- choose (0, size - 1)
        conn <- oneof $ map return [And, Or, Implies, Iff]
        left <- f $ size'
        right <- f $ size - size' - 1
        return $ conn left right),
      (5, do
        conn <- oneof $ map return [Exists, Forall]
        phi <- f $ size - 1
        x <- arbitrary
        return $ conn x phi)
      ]

  shrink (Not varphi) = [varphi]
  shrink (Or varphi psi) = [varphi, psi]
  shrink (And varphi psi) = [varphi, psi]
  shrink (Implies varphi psi) = [varphi, psi]
  shrink (Iff varphi psi) = [varphi, psi]
  shrink (Exists _ varphi) = [varphi]
  shrink (Forall _ varphi) = [varphi]
  shrink _ = []


phifun = Exists "x" (Rel "R" [Fun "f" [Var "x", Var "y"], Var "z"])
prop_fv = fv phifun == ["y", "z"]



-- Skolemization --------------------------------------------------------------
prop_generalise = generalise (Exists "x" (Rel "R" [Fun "f" [Var "x", Var "y"], Var "z"])) == Forall "y" (Forall "z" (Exists "x" (Rel "R" [Fun "f" [Var "x",Var "y"],Var "z"])))


prop_skolem_1 = skolemize (Forall "x" $ Exists "y" $ Rel "P" [Var "x", Var "y"] /\ Rel "Q" [Var "y"]) == Forall "x" (And (Rel "P" [Var "x", Fun "y" [Var "x"]]) (Rel "Q" [Fun "y" [Var "x"]]))


-- Conversion -----------------------------------------------------------------
quantFree :: Formula -> Bool
quantFree alpha = case alpha of
    F               -> True
    T               -> True

    Rel _ _         -> True
    Not     phi     -> quantFree phi
    
    Or      phi psi -> quantFree phi && quantFree psi
    And     phi psi -> quantFree phi && quantFree psi
    Implies phi psi -> quantFree phi && quantFree psi
    Iff     phi psi -> quantFree phi && quantFree psi
    
    Exists _ _      -> False
    Forall _ _      -> False

-- this is just to generate a quantifier free formula, 
-- no need of preserving any properties like satisfiablility etc.
removeQuants :: Formula -> Formula 
removeQuants alpha = case alpha of
    Not     phi     -> Not $ removeQuants phi
    
    Or      phi psi -> Or       (removeQuants phi) (removeQuants psi)
    And     phi psi -> And      (removeQuants phi) (removeQuants psi)
    Implies phi psi -> Implies  (removeQuants phi) (removeQuants psi)
    Iff     phi psi -> Iff      (removeQuants phi) (removeQuants psi)
    
    Exists x phi    -> removeQuants phi
    Forall x phi    -> removeQuants phi

    _               -> alpha

prop_removeQuants_works :: Formula -> Bool
prop_removeQuants_works phi = quantFree $ removeQuants phi

prop_conversion_works_1 :: Formula -> Bool
prop_conversion_works_1 alpha = let
    phi = removeQuants alpha
    (propToAtomic, atomicToProp) = assignProps phi

    phiClone = propToFO propToAtomic $ quantFreeFOToProp atomicToProp phi

  in phiClone == phi


prop_conversion_works_2 :: Prop.Formula -> Bool
prop_conversion_works_2 phi = let

    (propToAtomic, atomicToProp) = assignAtomics phi
    phiClone = quantFreeFOToProp atomicToProp $ propToFO propToAtomic phi

  in phiClone == phi




main :: IO ()
main = putStrLn "Test FirstOrder"
    >> quickCheck prop_fv
    >> quickCheck prop_generalise
    >> quickCheck prop_skolem_1

    -- test a test helper function
    >> quickCheck prop_removeQuants_works
    >> quickCheck prop_conversion_works_1
    >> quickCheck prop_conversion_works_2


