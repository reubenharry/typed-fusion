{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Site-by-site variational probe for L→C→R DMRG (productMPS TFIM).
--
-- For each site: energy before/after gauge, HS Rayleigh, Lanczos λ / residual,
-- network ΔE. On the right site also compares 'groundStateDense'.
--
--   cabal run dmrg-site-variational
import Prelude hiding (($))
import Control.Arrow.Constrained (($))
import Control.Lens ((^.), (.~), (&), _1)
import Data.Complex (Complex ((:+)), magnitude, realPart)
import Data.VectorSpace (AdditiveGroup ((^-^)), InnerSpace ((<.>)), VectorSpace ((*^)))
import Numeric.LinearAlgebra.Static (C)
import System.Exit (exitFailure, exitSuccess)

import GroundState (groundStateDense)
import Lanczos (groundStateLanczos)
import TensorNetwork.DMRG.Fixed
  ( centreDimBulk, centreDimLeft, centreDimRight, energy
  , heffBulk, heffLeft, heffRight, productMPS, tfimMPO
  )
import TensorNetwork.MPS.General
  ( FullNorm, hermitianNorm, mixedCanonicalCentre3, mixedCanonicalLeft3
  , mixedCanonicalRight3, mpsBulk, mpsInner, mpsLeft, mpsRight
  )

rayleighHS heff c =
  let n = c <.> c
  in realPart ((c <.> (heff $ c)) / n)

residualHS heff lam c =
  let r = (heff $ c) ^-^ ((lam :+ 0) *^ c)
  in sqrt (realPart (r <.> r))

reportSite
  :: String
  -> Double
  -> Double
  -> Double
  -> Double
  -> Double
  -> Double
  -> Double
  -> IO Bool
reportSite name ePreGauge ePostGauge r0 lam r1 res eAfter = do
  putStrLn ("== " ++ name ++ " ==")
  putStrLn ("  E before gauge     = " ++ show ePreGauge)
  putStrLn ("  E after gauge      = " ++ show ePostGauge)
  putStrLn ("  ΔE(gauge)          = " ++ show (ePostGauge - ePreGauge))
  putStrLn ("  HS Rayleigh before = " ++ show r0)
  putStrLn ("  Lanczos λ          = " ++ show lam)
  putStrLn ("  HS Rayleigh after  = " ++ show r1)
  putStrLn ("  ‖Heff c − λ c‖_HS  = " ++ show res)
  putStrLn ("  E after solve      = " ++ show eAfter)
  putStrLn ("  ΔE(solve)          = " ++ show (eAfter - ePostGauge))
  let okGauge = abs (ePostGauge - ePreGauge) < 1e-8
      okLam = abs (lam - r1) < 1e-6
      okRes = res < 1e-6
      okVar = eAfter <= ePostGauge + 1e-8
  putStrLn ("  gauge preserves E? " ++ show okGauge)
  putStrLn ("  λ ≈ Rayleigh?      " ++ show okLam)
  putStrLn ("  residual small?    " ++ show okRes)
  putStrLn ("  solve lowers E?    " ++ show okVar)
  putStrLn ""
  pure (okGauge && okLam && okRes && okVar)

main :: IO ()
main = do
  let nb = hermitianNorm :: FullNorm (C 3)
      np = hermitianNorm :: FullNorm (C 2)
      mpo = tfimMPO @1 1 0.7
      psi0 = productMPS @1
      e0 = energy nb np mpo psi0

  putStrLn ("initial E = " ++ show e0)
  putStrLn ("‖ψ‖²      = " ++ show (mpsInner nb np psi0 psi0))
  putStrLn ""

  -- Left
  let ePreL = energy nb np mpo psi0
      psiLg = mixedCanonicalLeft3 psi0
      ePostL = energy nb np mpo psiLg
      heffL = heffLeft nb np psiLg mpo
      cL0 = psiLg ^. mpsLeft
      rL0 = rayleighHS heffL cL0
      (lamL, cL1) = groundStateLanczos (centreDimLeft @3 @2) cL0 heffL
      psiL1 = psiLg & mpsLeft .~ cL1
      eL1 = energy nb np mpo psiL1
      rL1 = rayleighHS heffL cL1
      resL = residualHS heffL lamL cL1
  okL <- reportSite "Left" ePreL ePostL rL0 lamL rL1 resL eL1

  -- Bulk
  let ePreC = energy nb np mpo psiL1
      psiCg = mixedCanonicalCentre3 psiL1
      ePostC = energy nb np mpo psiCg
      heffC = heffBulk nb np 0 psiCg mpo
      cC0 = psiCg ^. mpsBulk . _1
      rC0 = rayleighHS heffC cC0
      zC = mpsInner nb np psiCg psiCg
      (lamC, cC1) = groundStateLanczos (centreDimBulk @3 @2) cC0 heffC
      psiC1 = psiCg & mpsBulk . _1 .~ cC1
      eC1 = energy nb np mpo psiC1
      rC1 = rayleighHS heffC cC1
      resC = residualHS heffC lamC cC1
  putStrLn ("  |mpsInner − ‖c‖²_HS| (centre gauge) = "
            ++ show (magnitude (zC - (cC0 <.> cC0))))
  okC <- reportSite "Bulk" ePreC ePostC rC0 lamC rC1 resC eC1

  -- Right
  let ePreR = energy nb np mpo psiC1
      psiRg = mixedCanonicalRight3 psiC1
      ePostR = energy nb np mpo psiRg
      heffR = heffRight nb np psiRg mpo
      cR0 = psiRg ^. mpsRight
      rR0 = rayleighHS heffR cR0
      zR = mpsInner nb np psiRg psiRg
      (lamR, cR1) = groundStateLanczos (centreDimRight @3 @2) cR0 heffR
      psiR1 = psiRg & mpsRight .~ cR1
      eR1 = energy nb np mpo psiR1
      rR1 = rayleighHS heffR cR1
      resR = residualHS heffR lamR cR1
  putStrLn ("  |mpsInner − ‖c‖²_HS| (right gauge) = "
            ++ show (magnitude (zR - (cR0 <.> cR0))))
  okR <- reportSite "Right (Lanczos)" ePreR ePostR rR0 lamR rR1 resR eR1

  -- Dense oracle on the same right Heff / state
  let (lamD, cD) = groundStateDense heffR
      psiD = psiRg & mpsRight .~ cD
      eD = energy nb np mpo psiD
      rD = rayleighHS heffR cD
      resD = residualHS heffR lamD cD
  putStrLn "== Right (dense oracle, same Heff) =="
  putStrLn ("  dense λ            = " ++ show lamD)
  putStrLn ("  HS Rayleigh after  = " ++ show rD)
  putStrLn ("  ‖Heff c − λ c‖_HS  = " ++ show resD)
  putStrLn ("  E after dense      = " ++ show eD)
  putStrLn ("  ΔE(dense)          = " ++ show (eD - ePostR))
  putStrLn ("  |λ_Lanz − λ_dense| = " ++ show (abs (lamR - lamD)))
  let okDenseVar = eD <= ePostR + 1e-8
      okMatch = abs (lamR - lamD) < 1e-6
  putStrLn ("  dense lowers E?    " ++ show okDenseVar)
  putStrLn ("  Lanczos ≈ dense λ? " ++ show okMatch)
  putStrLn ""

  putStrLn "Summary:"
  putStrLn ("  left ok?           " ++ show okL)
  putStrLn ("  bulk ok?           " ++ show okC)
  putStrLn ("  right Lanczos ok?  " ++ show okR)
  putStrLn ("  right dense lowers?" ++ show okDenseVar)

  if okL && okC && okR
    then putStrLn "ALL SITE STEPS VARIATIONAL" >> exitSuccess
    else do
      putStrLn "STOPPED: non-variational site step (see above)"
      if not okR && not okDenseVar
        then putStrLn "NOTE: dense also raises E → gauge/env/Heff-right, not Lanczos."
        else if not okR && okDenseVar
          then putStrLn "NOTE: dense lowers E but Lanczos does not → solver mismatch."
          else pure ()
      exitFailure
