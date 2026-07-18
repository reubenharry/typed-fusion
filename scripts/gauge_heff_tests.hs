{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Slow-and-steady DMRG component checks on the 3-site chain (χ=3, p=2):
--
--   1. mixed-canonical gauge preserves the flat physical tensor
--   2. the effective Hamiltonian reproduces ⟨ψ|H|ψ⟩
--   3. solving at the centre site is consistent and lowers the energy
import Prelude hiding (($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($))
import Control.Lens ((^.), _1)
import Data.Complex (Complex, realPart, magnitude)
import Data.VectorSpace (InnerSpace ((<.>)), (^-^))
import Numeric.LinearAlgebra.Static (C)

import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

import TensorNetwork.MPS.Fixed (genMPSC)
import TensorNetwork.MPS.General
import TensorNetwork.DMRG.Fixed (tfimMPO, energy, heffBulk, solveBulk)
import GroundState (groundState)

flat :: MPS (C 3) (C 2) 1 -> C 8
flat psi = physical3ToFlat @2 $ toPhysicalMPS hermitianNorm psi

vecDiff :: C 8 -> C 8 -> Double
vecDiff a b = sqrt (realPart ((a ^-^ b) <.> (a ^-^ b)))

check :: String -> Double -> IO ()
check label err = do
  let verdict = if err < 1e-9 then "OK  " else "FAIL"
  putStrLn $ verdict ++ "  " ++ label ++ "  (err = " ++ show err ++ ")"

main :: IO ()
main = do
  let psi0 = unGen (genMPSC @3 @2 @1) (mkQCGen 7) 30
      mpo = tfimMPO @1 1 0.7
      nb = hermitianNorm
      np = hermitianNorm

  putStrLn "== Test 1: mixed-canonical gauge preserves the flat tensor =="
  let psiG = mixedCanonicalCentre3 psi0
      f0 = flat psi0
      fG = flat psiG
  check "flat tensor invariant under gauge" (vecDiff f0 fG / sqrt (realPart (f0 <.> f0)))

  putStrLn ""
  putStrLn "== Test 2: Heff energy matches <psi|H|psi> =="
  let eRef = energy nb np mpo psiG
      centre = mpsBulk psiG ^. _1
      heffC = effectiveHBulk3 nb np psiG mpo centre
      eHeff = realPart (centre <.> heffC) / realPart (centre <.> centre)
  putStrLn $ "  energy via mpsMPOInner = " ++ show eRef
  putStrLn $ "  energy via Heff        = " ++ show eHeff
  check "Heff Rayleigh quotient = energy" (abs (eRef - eHeff))

  putStrLn ""
  putStrLn "== Test 3: centre solve is consistent and decreases energy =="
  let (eSolved, centre') = groundState (heffBulk nb np 0 psiG mpo)
      psi' = mpsWithBulkSite centre' psiG
      eAfter = energy nb np mpo psi'
  putStrLn $ "  energy before solve      = " ++ show eRef
  putStrLn $ "  eigenvalue from solve    = " ++ show eSolved
  putStrLn $ "  energy of updated MPS    = " ++ show eAfter
  check "solve decreased energy" (max 0 (eSolved - eRef))
  check "updated-MPS energy = eigenvalue" (abs (eAfter - eSolved))
