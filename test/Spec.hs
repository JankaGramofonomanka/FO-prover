
import qualified Propositional.Testing as Prop
import qualified FirstOrder.Testing as FO

main :: IO ()
main = Prop.main
    >> FO.main
