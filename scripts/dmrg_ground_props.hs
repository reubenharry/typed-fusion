{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

-- | DMRG converges to the dense three-site TFIM ground energy from random MPS.
--
--   cabal run dmrg-ground-props
import System.Exit (exitFailure, exitSuccess)
import Test.QuickCheck (Result (..), quickCheckResult, withMaxSuccess)

import TensorNetwork.DMRG.Fixed
  ( denseTfimGroundEnergy, prop_dmrgConvergesFromRandomMPS
  )

main :: IO ()
main = do
  putStrLn ("dense TFIM ground (J=1,h=0.7) = " ++ show (denseTfimGroundEnergy 1 0.7))
  putStrLn "prop_dmrgConvergesFromRandomMPS (25 tests)..."
  -- Each test runs up to 8 sweeps; keep the suite under ~1–2 minutes.
  r <- quickCheckResult $ withMaxSuccess 25 prop_dmrgConvergesFromRandomMPS
  case r of
    Success{} -> putStrLn "OK" >> exitSuccess
    _ -> do
      print r
      exitFailure
