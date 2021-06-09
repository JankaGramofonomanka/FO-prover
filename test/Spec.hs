
import qualified Propositional.Testing as Prop
import qualified FirstOrder.Testing as FO
import qualified Testing as Global

main :: IO ()
main = Prop.main
    >> FO.main
    >> Global.main
