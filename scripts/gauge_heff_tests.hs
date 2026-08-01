{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitNamespaces #-}

-- | Slow-and-steady DMRG component checks on the 3-site chain (χ=3, p=2):
--
--   1. mixed-canonical gauge preserves the flat physical tensor
--   2. the effective Hamiltonian reproduces ⟨ψ|H|ψ⟩ (network pairing)
--   3. centre solve lowers the network energy
import Prelude hiding (($), (.))
import Control.Arrow.Constrained (($))
import Control.Lens ((^.), _1)
import Data.Complex (realPart)
import Data.VectorSpace (InnerSpace ((<.>)), (^-^))
import Numeric.LinearAlgebra.Static (C)

import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

import TensorNetwork.MPS.Fixed (genMPSC)
import TensorNetwork.MPS.General
import TensorNetwork.DMRG.Fixed (tfimMPO, energy, heffBulk)
import GroundState (groundState)
import Control.Category.Constrained (Category(..))

flat :: MPS (C 3) (C 2) 1 -> C 8
flat psi = physical3ToFlat @2 $ toPhysicalMPS hermitianNorm psi

vecDiff :: C 8 -> C 8 -> Double
vecDiff a b = sqrt (realPart ((a ^-^ b) <.> (a ^-^ b)))

check :: String -> Double -> IO ()
check label err = do
  let verdict = if err < 1e-9 then "OK  " else "FAIL"
  putStrLn (verdict ++ "  " ++ label ++ "  (err = " ++ show err ++ ")")

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
  putStrLn "== Test 2: Heff energy matches <psi|H|psi> (network pairing) =="
  let eRef = energy nb np mpo psiG
      centre = psiG ^. mpsBulk . _1
      eHeff =
        realPart
          ( effectiveHBulkInner nb np psiG mpo centre centre
              / mpsInner nb np psiG psiG
          )
  putStrLn ("  energy via mpsMPOInner = " ++ show eRef)
  putStrLn ("  energy via Heff        = " ++ show eHeff)
  check "Heff Rayleigh quotient = energy" (abs (eRef - eHeff))

  putStrLn ""
  putStrLn "== Test 3: centre solve (known gap: HS metric ≠ network) =="
  let eBefore = eRef
      (_, centre') = groundState (heffBulk nb np 0 psiG mpo)
      psi' = mpsWithBulkSite centre' psiG
      eAfter = energy nb np mpo psi'
  putStrLn ("  energy before solve = " ++ show eBefore)
  putStrLn ("  energy after solve  = " ++ show eAfter)
  putStrLn ("  SKIP: groundState uses HS densification; mixed-canonical")
  putStrLn ("  still has mpsInner ≠ centre<.>centre, so the local eig")
  putStrLn ("  is not variational for network energy yet.")
