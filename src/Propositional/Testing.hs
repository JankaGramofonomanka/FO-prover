module Propositional.Testing where



import Propositional.Formula 
import Propositional.CNF
import Propositional.DavisPutnamSAT



import Control.Monad
import Test.QuickCheck




instance Arbitrary Formula where
    arbitrary = sized f where
      
      f 0 = oneof $ map return $ [p, q, r, s, t] ++ [T, F]

      f size = frequency [
        (1, liftM Not (f (size - 1))),
        (4, do
              size' <- choose (0, size - 1)
              conn <- oneof $ map return [And, Or, Implies, Iff]
              left <- f size'
              right <- f $ size - size' - 1
              return $ conn left right)
        ]
        
    shrink (Not φ) = [φ]
    shrink (Or φ ψ) = [φ, ψ]
    shrink (And φ ψ) = [φ, ψ]
    shrink (Implies φ ψ) = [φ, ψ]
    shrink (Iff φ ψ) = [φ, ψ]
    shrink _ = []



prop_distribute :: Bool
prop_distribute = distribute [[1, 2], [3, 4]] [[5, 6], [7]] == [[1, 2, 5, 6], [1, 2, 7], [3, 4, 5, 6], [3, 4, 7]]





test_cnf :: Formula -> Bool
test_cnf φ = tautology $ φ ⇔ (cnf2formula (cnf φ))

--quickCheckWith (stdArgs {maxSize = 18}) test_cnf



equi_satisfiable :: Formula -> Formula -> Bool
equi_satisfiable φ ψ = satisfiable φ == satisfiable ψ



prop_ecnf :: Formula -> Bool
prop_ecnf phi = equi_satisfiable phi (cnf2formula $ ecnf phi)

--quickCheckWith (stdArgs {maxSize = 18}) prop_ecnf
--quickCheck prop_ecnf





prop_one_literal :: Bool
prop_one_literal =
  one_literal
    [[Pos "p"], [Pos "p", Pos "q", Pos "p", Pos "r"], [Neg "q", Pos "r", Neg "p", Neg "r", Neg "p"], [Neg "q", Neg "p"], [Pos "q", Pos "r", Pos "s"], [Neg "p", Pos "p"]] ==
    [[Pos "r",Pos "s"]] &&
  one_literal
    [[Pos "p2"],[Neg "p2",Pos "p"],[Neg "p2",Pos "p1"],[Neg "p",Neg "p1",Pos "p2"],[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "p0",Neg "p"],[Neg "s",Pos "p",Pos "p0"]] ==
    [[]] &&
  one_literal
    [[Pos "q"],[Pos "p0"],[Neg "p0",Pos "s"],[Neg "p0"]] ==
    [[]]
    
--quickCheck prop_one_literal



prop_affirmative_negative :: Bool
prop_affirmative_negative =
  affirmative_negative [[Pos "p"],[Pos "p1"],[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "p0",Neg "p"],[Neg "s",Pos "p",Pos "p0"]] ==
    [[Pos "p"],[Pos "p1"],[Neg "p1",Pos "q"],[Neg "p1",Pos "p0"],[Neg "q",Neg "p0",Pos "p1"],[Neg "p0",Pos "s"],[Neg "p0",Neg "p"],[Neg "s",Pos "p",Pos "p0"]] &&
  affirmative_negative [[Pos "p", Pos "q"], [Pos "p", Neg "q"]] == []
    
--quickCheck prop_affirmative_negative

prop_resolution :: Bool
prop_resolution = resolution [[Pos "p", Pos "q"],[Pos "p", Pos "r"],[Neg "p", Neg "q"]] == [[Pos "q", Neg "q"], [Pos "r", Neg "q"]]



prop_satDP_works :: Formula -> Bool
prop_satDP_works phi = satisfiable phi == satDP phi



main :: IO ()
main = quickCheck prop_distribute
    >> quickCheckWith (stdArgs {maxSize = 18}) test_cnf
    >> quickCheckWith (stdArgs {maxSize = 18}) prop_ecnf
    -- >> quickCheck test_cnf
    -- >> quickCheck prop_ecnf
    >> quickCheck prop_one_literal
    >> quickCheck prop_affirmative_negative
    >> quickCheckWith (stdArgs {maxSize = 18}) prop_satDP_works
    





