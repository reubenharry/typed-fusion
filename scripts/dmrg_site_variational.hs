{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitNamespaces #-}

-- | Failing test + diagnosis: bulk DMRG site step can raise network energy.
--
-- Witness: TFIM seed 7, solve left then re-gauge to centre, then bulk solve.
-- Metric/pairing identities hold; 'groundStateSimple' ('eigen' + HS norm)
-- returns a vector whose true HS Rayleigh is *higher* than before, while the
-- reported eigenvalue is unrelated. 'groundStateDense' on the same Heff
-- lowers both HS Rayleigh and network energy.
--
--   cabal run dmrg-site-variational
import Prelude hiding (($))
import Control.Arrow.Constrained (($))
import Control.Lens ((^.), (.~), (&), _1)
import Data.Complex (Complex, magnitude, realPart)
import Data.VectorSpace (InnerSpace ((<.>)))
import System.Exit (exitFailure, exitSuccess)
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

import GroundState (groundStateDense, groundStateSimple)
import TensorNetwork.DMRG.Fixed
  ( energy, heffBulk, heffLeft, tfimMPO )
import TensorNetwork.MPS.Fixed (genMPSC)
import TensorNetwork.MPS.General
  ( effectiveHBulkInner, hermitianNorm, mixedCanonicalCentre3
  , mixedCanonicalLeft3, mpsBulk, mpsInner, mpsLeft, mpsWithBulkSite
  )

mag :: Complex Double -> Double
mag = magnitude

rayleighHS heff c =
  let n = c <.> c
  in realPart ((c <.> (heff $ c)) / n)

main :: IO ()
main = do
  let nb = hermitianNorm
      np = hermitianNorm
      mpo = tfimMPO @1 1 0.7
      psi0 = unGen (genMPSC @3 @2 @1) (mkQCGen 7) 30
      psiL0 = mixedCanonicalLeft3 psi0
      (_, sL) = groundStateSimple (heffLeft nb np psiL0 mpo)
      psiL1 = psiL0 & mpsLeft .~ sL
      psiC0 = mixedCanonicalCentre3 psiL1
      c0 = psiC0 ^. mpsBulk . _1
      heff = heffBulk nb np 0 psiC0 mpo
      e0 = energy nb np mpo psiC0
      r0 = rayleighHS heff c0

      (lamS, cS) = groundStateSimple heff
      psiS = mpsWithBulkSite cS psiC0
      eS = energy nb np mpo psiS
      rS = rayleighHS heff cS

      (lamD, cD) = groundStateDense heff
      psiD = mpsWithBulkSite cD psiC0
      eD = energy nb np mpo psiD
      rD = rayleighHS heff cD

  putStrLn "== Bulk centre after left solve + mixedCanonicalCentre3 =="
  putStrLn ("  E_network before     = " ++ show e0)
  putStrLn ("  HS Rayleigh before   = " ++ show r0)
  putStrLn ("  |mpsInner − ‖c‖²_HS| = "
            ++ show (mag (mpsInner nb np psiC0 psiC0 - (c0 <.> c0))))
  putStrLn ("  |Inner − HS⟨Heff⟩|   = "
            ++ show (mag (effectiveHBulkInner nb np psiC0 mpo c0 c0
                            - (c0 <.> (heff $ c0)))))

  putStrLn ""
  putStrLn "== groundStateSimple (eigen + densifyNorm HS) =="
  putStrLn ("  reported λ           = " ++ show lamS)
  putStrLn ("  true HS Rayleigh     = " ++ show rS)
  putStrLn ("  |λ − Rayleigh|       = " ++ show (abs (lamS - rS)))
  putStrLn ("  E_network after      = " ++ show eS)
  putStrLn ("  ΔE                   = " ++ show (eS - e0))
  putStrLn ("  Δ HS Rayleigh        = " ++ show (rS - r0))

  putStrLn ""
  putStrLn "== groundStateDense (eigSH on toDenseMatrix) =="
  putStrLn ("  reported λ           = " ++ show lamD)
  putStrLn ("  true HS Rayleigh     = " ++ show rD)
  putStrLn ("  |λ − Rayleigh|       = " ++ show (abs (lamD - rD)))
  putStrLn ("  E_network after      = " ++ show eD)
  putStrLn ("  ΔE                   = " ++ show (eD - e0))
  putStrLn ("  Δ HS Rayleigh        = " ++ show (rD - r0))

  putStrLn ""
  let simpleRaises = eS > e0 + 1e-8
      simpleLamWrong = abs (lamS - rS) > 1e-4
      denseOk = eD <= e0 + 1e-8 && abs (lamD - rD) <= 1e-6
  putStrLn "Checks:"
  putStrLn ("  simple raises network E?     " ++ show simpleRaises)
  putStrLn ("  simple λ ≠ true HS Rayleigh? " ++ show simpleLamWrong)
  putStrLn ("  dense lowers E and λ matches?" ++ show denseOk)

  if simpleRaises && simpleLamWrong && denseOk
    then do
      putStrLn ""
      putStrLn "FAIL reproduced: groundStateSimple/eigen is not the HS ground"
      putStrLn "state of Heff; dense eigSH is. DMRG must not use simple here."
      exitFailure
    else if simpleRaises
      then do
        putStrLn ""
        putStrLn "FAIL: simple raises energy (see numbers; pattern unexpected)."
        exitFailure
      else do
        putStrLn "Unexpected pattern on this seed."
        exitSuccess
