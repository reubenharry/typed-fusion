{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
import TensorNetwork.DMRG.Fixed
import TensorNetwork.MPS.General (hermitianNorm)

main :: IO ()
main = do
  let mpo = tfimMPO @1 1 0.7
      psi = productMPS @1
      e0 = energy hermitianNorm hermitianNorm mpo psi
      r = dmrg @3 @2 @1 2 1e-6 mpo psi
  putStrLn $ "initial energy = " ++ show e0
  putStrLn $ "final energy   = " ++ show (dmrgFinalEnergy r)
  putStrLn $ "sweep energies = " ++ show (dmrgSweepEnergies r)
