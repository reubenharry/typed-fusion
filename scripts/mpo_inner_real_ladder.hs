{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}

-- | Break down “Im ⟨ψ|H|ψ⟩ ≠ 0” for complex genMPSC + TFIM.
--
--   1a. mpsInner sesquilinear hermiticity
--   1b. physical sandwich ⟨ψ|H|ψ⟩_phys real + densified H Hermitian
--   1c. transfer mpsMPOInner == physical sandwich
--   1d. transfer hermiticity ⟨ψ|H|φ⟩ = conj⟨φ|H|ψ⟩
--
--   cabal run mpo-inner-real-ladder
import Prelude hiding (($), (.))
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($))
import Data.Complex (Complex, conjugate, imagPart, magnitude, realPart)
import Data.VectorSpace (InnerSpace ((<.>)))
import Math.LinearMap.Category (type (+>), getLinearMap)
import Numeric.LinearAlgebra.Static (C, Sized (extract))
import qualified Numeric.LinearAlgebra as H
import System.Exit (exitFailure, exitSuccess)
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

import TensorNetwork.DMRG.Fixed (tfimMPO)
import TensorNetwork.MPS.Fixed (genMPSC)
import TensorNetwork.MPS.General
  ( FullNorm, hermitianNorm, mpsInner, mpsMPOInner
  , toPhysicalMPS, toPhysicalMPO, physical3ToFlat, physical3FromFlat
  )

approxEqC :: Complex Double -> Complex Double -> Bool
approxEqC a b = magnitude (a - b) <= 1e-8 * (1 + magnitude a + magnitude b)

reportC :: String -> Complex Double -> Complex Double -> IO Bool
reportC label lhs rhs = do
  let ok = approxEqC lhs rhs
  putStrLn (if ok then "OK  " else "FAIL")
  putStrLn ("  " ++ label)
  putStrLn ("  lhs = " ++ show lhs)
  putStrLn ("  rhs = " ++ show rhs)
  putStrLn ("  |Δ| = " ++ show (magnitude (lhs - rhs)))
  pure ok

reportOk :: String -> Bool -> IO Bool
reportOk label ok = do
  putStrLn (if ok then "OK  " else "FAIL")
  putStrLn ("  " ++ label)
  pure ok

-- | @hmatrix@ 'tr' is already conjugate-transpose for complex matrices.
frobHerm :: H.Matrix (Complex Double) -> Double
frobHerm m = H.norm_Frob (m - H.tr m)

main :: IO ()
main = do
  let nb = hermitianNorm :: FullNorm (C 3)
      np = hermitianNorm :: FullNorm (C 2)
      mpo = tfimMPO @1 1 0.7
      psi = unGen (genMPSC @3 @2 @1) (mkQCGen 7) 30
      phi = unGen (genMPSC @3 @2 @1) (mkQCGen 11) 30
      physPsi = toPhysicalMPS np psi
      physPhi = toPhysicalMPS np phi
      hPhys = toPhysicalMPO mpo
      hFlat =
        physical3ToFlat @2
          . hPhys
          . physical3FromFlat @2
      hM = extract (getLinearMap hFlat)
      sandwich p =
        let v = toPhysicalMPS np p
        in v <.> (hPhys $ v) :: Complex Double
      transfer p = mpsMPOInner nb np p mpo p

  putStrLn "== 1a: mpsInner hermiticity =="
  let zψφ = mpsInner nb np psi phi
      zφψ = mpsInner nb np phi psi
  ok1a <- reportC "⟨ψ|φ⟩ vs conj⟨φ|ψ⟩" zψφ (conjugate zφψ)
  ok1aDiag <- reportOk "Im ⟨ψ|ψ⟩ ≈ 0" (abs (imagPart (mpsInner nb np psi psi)) < 1e-8)
  if not (ok1a && ok1aDiag) then putStrLn "\nSTOPPED at 1a" >> exitFailure else putStrLn ""

  putStrLn "== 1b: physical ⟨ψ|H|ψ⟩ real + densified H Hermitian =="
  let ePhys = sandwich psi
      fh = frobHerm hM
  putStrLn ("  physical ⟨ψ|H|ψ⟩ = " ++ show ePhys)
  putStrLn ("  ‖H_phys−H†‖_F   = " ++ show fh)
  ok1bReal <- reportOk "Im physical ⟨ψ|H|ψ⟩ ≈ 0"
    (abs (imagPart ePhys) < 1e-6 * (1 + abs (realPart ePhys)))
  ok1bHerm <- reportOk "‖H_phys−H†‖_F < 1e-6" (fh < 1e-6)
  -- physical form hermiticity on two states
  let eψφ = physPsi <.> (hPhys $ physPhi) :: Complex Double
      eφψ = physPhi <.> (hPhys $ physPsi) :: Complex Double
  ok1bForm <- reportC "phys ⟨ψ|H|φ⟩ vs conj⟨φ|H|ψ⟩" eψφ (conjugate eφψ)
  if not (ok1bReal && ok1bHerm && ok1bForm)
    then putStrLn "\nSTOPPED at 1b (MPO/physical not Hermitian)" >> exitFailure
    else putStrLn ""

  putStrLn "== 1c: transfer == physical sandwich =="
  let eTrans = transfer psi
  putStrLn ("  transfer ⟨ψ|H|ψ⟩ = " ++ show eTrans)
  ok1c <- reportC "mpsMPOInner vs physical sandwich" eTrans ePhys
  if not ok1c then putStrLn "\nSTOPPED at 1c" >> exitFailure else putStrLn ""

  putStrLn "== 1d: transfer form hermiticity =="
  let tψφ = mpsMPOInner nb np psi mpo phi
      tφψ = mpsMPOInner nb np phi mpo psi
  ok1d <- reportC "transfer ⟨ψ|H|φ⟩ vs conj⟨φ|H|ψ⟩" tψφ (conjugate tφψ)
  ok1dDiag <- reportOk "Im transfer ⟨ψ|H|ψ⟩ ≈ 0"
    (abs (imagPart eTrans) < 1e-6 * (1 + abs (realPart eTrans)))
  if not (ok1d && ok1dDiag)
    then putStrLn "\nSTOPPED at 1d" >> exitFailure
    else putStrLn "\nALL SUBSTEPS OK" >> exitSuccess
