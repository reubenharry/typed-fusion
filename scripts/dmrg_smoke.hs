{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

-- | Smoke: TFIM DMRG with dense local solves should lower energy.
--   cabal run dmrg-smoke
import TensorNetwork.DMRG.Fixed
  ( dmrg, dmrgFinalEnergy, dmrgSweepEnergies, energy, productMPS, tfimMPO )
import TensorNetwork.MPS.General (hermitianNorm)
import System.Exit (exitFailure, exitSuccess)

main :: IO ()
main = do
  let mpo = tfimMPO @1 1 0.7
      psi = productMPS @1
      nb = hermitianNorm
      np = hermitianNorm
      e0 = energy nb np mpo psi
      r = dmrg @3 @2 @1 2 1e-6 mpo psi
      e1 = dmrgFinalEnergy r
      hist = dmrgSweepEnergies r
  putStrLn ("initial energy = " ++ show e0)
  putStrLn ("final energy   = " ++ show e1)
  putStrLn ("sweep energies = " ++ show hist)
  putStrLn ("ΔE             = " ++ show (e1 - e0))
  let nonIncreasing =
        and [ a <= b + 1e-8 | (b, a) <- zip hist (drop 1 hist) ]
  if e1 < e0 - 1e-8 && nonIncreasing
    then do
      putStrLn "OK: energy decreased and site steps non-increasing"
      exitSuccess
    else do
      putStrLn "FAIL: energy did not monotonically improve"
      exitFailure
