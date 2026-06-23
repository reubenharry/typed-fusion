import GroundState (smokeRandomEffectiveHamiltonian)
import TensorNetwork.DMRG.Fixed3 (smokeNetworkEffectiveHamiltonian)

main :: IO ()
main = do
  smokeRandomEffectiveHamiltonian
  putStrLn ""
  smokeNetworkEffectiveHamiltonian
