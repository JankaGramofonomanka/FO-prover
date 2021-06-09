module Testing where

import Test.QuickCheck

import qualified Propositional.Formula as Prop
import qualified Propositional.Testing as PropTest
import Propositional.DavisPutnamSAT
import Propositional.CNF
import FirstOrder.Conversion
import Prover


prover_works_1 :: Prop.Formula -> Bool
prover_works_1 phi = let

    (propToAtomic, atomicToProp) = assignAtomics phi
    foPhi = propToFO propToAtomic phi

  in Prop.tautology phi == prover foPhi





main :: IO ()
main = putStrLn "Test Global"
    >> quickCheckWith (stdArgs {maxSize = 5}) prover_works_1

