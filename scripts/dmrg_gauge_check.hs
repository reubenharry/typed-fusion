{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

import TensorNetwork.DMRG.Fixed3
  ( regaugeDepartRight, rightGaugeMPS, toZipper, moveRight, solveCenterAt
  , theMPS, flatMaxDiff, tfimMPO, seededMPS222, energy
  , prop_regaugeAfterRightGaugePreservesMPS
  , prop_normalizeLeftAbsorb23, prop_normalizeLeftAbsorb12
  , normalizeLeft, absorbLeftBond
  )
import TensorNetwork.MPS.Fixed3 (genMPS222, mpsToFlat)
import TensorNetwork.MPS.Fixed3.Internal (mps3, withMPS3)
import Test.QuickCheck (quickCheckResult)
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

main :: IO ()
main = do
  putStrLn "=== regauge after rightGauge (QC) ==="
  print =<< quickCheckResult prop_regaugeAfterRightGaugePreservesMPS
  print =<< quickCheckResult prop_normalizeLeftAbsorb12
  print =<< quickCheckResult prop_normalizeLeftAbsorb23

  let mps = unGen genMPS222 (mkQCGen 0) 30
  withMPS3 mps $ \s1 s2 s3 -> do
    let flat0 = mpsToFlat mps
        (s1c, b12) = normalizeLeft s1
        (s2c, b23) = normalizeLeft s2
        d12 = flatMaxDiff flat0 (mpsToFlat (mps3 s1c (absorbLeftBond b12 s2) s3))
        d23 = flatMaxDiff flat0 (mpsToFlat (mps3 s1 s2c (absorbLeftBond b23 s3)))
    putStrLn $ "seed 0 flatΔ absorb 1→2: " ++ show d12
    putStrLn $ "seed 0 flatΔ absorb 2→3: " ++ show d23
