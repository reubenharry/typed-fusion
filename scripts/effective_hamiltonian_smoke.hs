import GroundState (smokeRandomEffectiveHamiltonian)
import TensorNetwork.DMRG.Fixed (smokeNetworkEffectiveHamiltonian)

main :: IO ()
main = do
  smokeRandomEffectiveHamiltonian
  putStrLn ""
  smokeNetworkEffectiveHamiltonian
