{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

-- | Minimal regression: after 'mixedCanonicalCentre3', transfer 'mpsInner ψ ψ'
-- must stay real and match the flattened physical oracle (and the gauge must
-- preserve that oracle).
--
--   cabal run mps-inner-not-real
--
-- Broader QuickCheck: 'prop_mpsInnerAfterMixedCanonical' via
--   cabal run mps-inner-props
import Prelude
import Data.Complex (Complex, imagPart, magnitude, realPart)
import Data.VectorSpace (InnerSpace ((<.>)), (^-^))
import System.Exit (exitFailure)

import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

import TensorNetwork.MPS.Fixed (genMPSC)
import TensorNetwork.MPS.General
  ( hermitianNorm, mixedCanonicalCentre3, mpsInner, toPhysicalMPS )

report :: String -> Complex Double -> IO ()
report label z = do
  putStrLn label
  putStrLn ("  ⟨ψ|ψ⟩      = " ++ show z)
  putStrLn ("  |Im| / |z| = " ++ show (abs (imagPart z) / max 1e-30 (magnitude z)))
  putStrLn ("  real?      = " ++ if isReal z then "yes" else "NO")

isReal :: Complex Double -> Bool
isReal z = abs (imagPart z) < 1e-9 * max 1 (magnitude z)

approxEq :: Complex Double -> Complex Double -> Bool
approxEq z w = magnitude (z - w) <= 1e-8 * (1 + magnitude z + magnitude w)

main :: IO ()
main = do
  let psi0 = unGen (genMPSC @3 @2 @1) (mkQCGen 7) 30
      psiG = mixedCanonicalCentre3 psi0
      nb = hermitianNorm
      np = hermitianNorm
      z0 = mpsInner nb np psi0 psi0
      zG = mpsInner nb np psiG psiG
      v0 = toPhysicalMPS np psi0
      vG = toPhysicalMPS np psiG
      o0 = v0 <.> v0
      oG = vG <.> vG
      flatDiff = sqrt (realPart ((v0 ^-^ vG) <.> (v0 ^-^ vG)))
      flatRel = flatDiff / sqrt (realPart o0)

  putStrLn "=== Before mixedCanonicalCentre3 ==="
  report "mpsInner (transfer)" z0
  report "oracle toPhysicalMPS <.>" o0

  putStrLn ""
  putStrLn "=== After mixedCanonicalCentre3 ==="
  report "mpsInner (transfer)" zG
  report "oracle toPhysicalMPS <.>" oG

  putStrLn ""
  putStrLn "=== Gauge / consistency ==="
  putStrLn ("  ||flat(ψ0) − flat(ψG)|| / ||flat|| = " ++ show flatRel)
  putStrLn ("  |mpsInner0 − oracle0| = " ++ show (magnitude (z0 - o0)))
  putStrLn ("  |mpsInnerG − oracleG| = " ++ show (magnitude (zG - oG)))
  putStrLn ("  |oracle0 − oracleG|   = " ++ show (magnitude (o0 - oG)))

  let ok =
        isReal z0
          && isReal zG
          && approxEq z0 o0
          && approxEq zG oG
          && approxEq o0 oG
          && approxEq z0 zG
          && flatRel < 1e-9
  if ok
    then putStrLn "\nOK"
    else do
      putStrLn "\nFAIL: transfer mpsInner / mixed-canonical gauge regression"
      exitFailure
