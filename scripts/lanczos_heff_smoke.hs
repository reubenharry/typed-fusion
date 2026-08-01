{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}

-- | Incremental ladder toward 'lanczosLowestQ' on TFIM bulk Heff (χ=3, p=2).
-- Stops at the first failing step.
--
--   1. ⟨ψ|H|ψ⟩ = mpsMPOInner is real (Hermitian H)
--   2. HS pairing = network pairing on centres
--   3. Heff HS-Hermitian (y⟨Heff x⟩ ≈ conj(x⟨Heff y⟩))
--   4. Q† ∘ Q ≈ id on BulkSite (Krylov m=2)
--   5. lanczosLowestQ ≈ groundStateDense
--
--   cabal run lanczos-heff-smoke
import Prelude hiding (($), (.))
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($), EnhancedCat (arr))
import Control.Lens ((^.), _1)
import Data.Complex (Complex ((:+)), conjugate, imagPart, magnitude, realPart)
import qualified Data.List.NonEmpty as NE
import Data.VectorSpace (AdditiveGroup ((^-^)), InnerSpace ((<.>)), VectorSpace ((*^)))
import GHC.TypeLits (type (*))
import Math.LinearMap.Category (type (+>), type (-+>))
import Numeric.LinearAlgebra.Static (C)
import qualified Numeric.LinearAlgebra as H
import System.Exit (exitFailure, exitSuccess)
import Test.QuickCheck.Gen (generate, unGen)
import Test.QuickCheck.Random (mkQCGen)

import GroundState (basisOf, groundStateDense, toDenseMatrix)
import Lanczos
  ( asMap
  , defaultLanczosTolerance
  , lanczosLowestQ
  , lanczosQ
  , lanczosQDag
  , lanczosTridiag
  )
import Random.Arbitrary (genLinMapC)
import TensorNetwork.Categorical (fuseBond)
import TensorNetwork.DMRG.Fixed (heffBulk, tfimMPO)
import TensorNetwork.MPS.Fixed (genMPSC)
import TensorNetwork.MPS.General
  ( BulkSite, FullNorm, MPS, MPO, effectiveHBulkInner, hermitianNorm
  , mixedCanonicalCentre3, mpsBulk, mpsInner, mpsMPOInner
  )

type Centre = BulkSite (C 3) (C 2)

approxEqC :: Complex Double -> Complex Double -> Bool
approxEqC a b = magnitude (a - b) <= 1e-8 * (1 + magnitude a + magnitude b)

approxEqD :: Double -> Double -> Bool
approxEqD a b = abs (a - b) <= 1e-6 * (1 + abs a + abs b)

reportC :: String -> Complex Double -> Complex Double -> IO Bool
reportC label lhs rhs = do
  let ok = approxEqC lhs rhs
  putStrLn (if ok then "OK  " else "FAIL")
  putStrLn ("  " ++ label)
  putStrLn ("  lhs = " ++ show lhs)
  putStrLn ("  rhs = " ++ show rhs)
  putStrLn ("  |Δ| = " ++ show (magnitude (lhs - rhs)))
  pure ok

reportD :: String -> Double -> Double -> IO Bool
reportD label lhs rhs = do
  let ok = approxEqD lhs rhs
  putStrLn (if ok then "OK  " else "FAIL")
  putStrLn ("  " ++ label)
  putStrLn ("  lhs = " ++ show lhs)
  putStrLn ("  rhs = " ++ show rhs)
  putStrLn ("  |Δ| = " ++ show (abs (lhs - rhs)))
  pure ok

genBulk :: IO Centre
genBulk = do
  flat <- generate (genLinMapC @(3 * 2) @3)
  pure (flat . fuseBond @3 @2)

-- | @hmatrix@ 'tr' is already conjugate-transpose for complex matrices.
frobHerm :: H.Matrix (Complex Double) -> Double
frobHerm m = H.norm_Frob (m - H.tr m)

data Ctx = Ctx
  { ctxPsi :: MPS (C 3) (C 2) 1
  , ctxMPO :: MPO (C 3) 1 (C 2) (C 2)
  , ctxNb :: FullNorm (C 3)
  , ctxNp :: FullNorm (C 2)
  , ctxHeff :: Centre +> Centre
  , ctxF :: Centre -+> Centre
  , ctxSeed :: Centre
  }

setup :: IO Ctx
setup = do
  let psi0 = unGen (genMPSC @3 @2 @1) (mkQCGen 7) 30
      psi = mixedCanonicalCentre3 psi0
      mpo = tfimMPO @1 1 0.7
      nb = hermitianNorm :: FullNorm (C 3)
      np = hermitianNorm :: FullNorm (C 2)
      heff = heffBulk nb np 0 psi mpo :: Centre +> Centre
      f = arr heff
      seed = psi ^. mpsBulk . _1
  pure (Ctx psi mpo nb np heff f seed)

step1 :: Ctx -> IO Bool
step1 Ctx{ctxPsi=psi, ctxMPO=mpo, ctxNb=nb, ctxNp=np} = do
  putStrLn "== Step 1: mpsMPOInner(ψ,H,ψ) is real =="
  let z = mpsInner nb np psi psi
      e = mpsMPOInner nb np psi mpo psi
  putStrLn ("  mpsInner    = " ++ show z)
  putStrLn ("  mpsMPOInner = " ++ show e)
  let okZ = abs (imagPart z) < 1e-8
      okE = abs (imagPart e) < 1e-6 * (1 + abs (realPart e))
  putStrLn (if okZ then "OK  " else "FAIL")
  putStrLn "  Im ⟨ψ|ψ⟩ ≈ 0"
  putStrLn (if okE then "OK  " else "FAIL")
  putStrLn "  Im ⟨ψ|H|ψ⟩ ≈ 0"
  pure (okZ && okE)

step2 :: Ctx -> IO Bool
step2 Ctx{ctxPsi=psi, ctxMPO=mpo, ctxNb=nb, ctxNp=np, ctxHeff=heff} = do
  putStrLn "== Step 2: HS pairing = network pairing =="
  x <- genBulk
  y <- genBulk
  let net = effectiveHBulkInner nb np psi mpo y x
      hs = y <.> (heff $ x) :: Complex Double
  reportC "B(y,x) vs y⟨Heff x⟩_HS" net hs

step3 :: Ctx -> IO Bool
step3 Ctx{ctxPsi=psi, ctxMPO=mpo, ctxNb=nb, ctxNp=np, ctxHeff=heff} = do
  putStrLn "== Step 3: Heff / network hermiticity =="
  x <- genBulk
  y <- genBulk
  let hsYX = y <.> (heff $ x) :: Complex Double
      hsXY = x <.> (heff $ y) :: Complex Double
      bYX = effectiveHBulkInner nb np psi mpo y x
      bXY = effectiveHBulkInner nb np psi mpo x y
      fh = frobHerm (toDenseMatrix heff)
  okHS <- reportC "y⟨Heff x⟩ vs conj(x⟨Heff y⟩)" hsYX (conjugate hsXY)
  okNet <- reportC "B(y,x) vs conj B(x,y)" bYX (conjugate bXY)
  putStrLn ("  ‖H−H†‖_F = " ++ show fh)
  let okFrob = fh < 1e-6
  putStrLn (if okFrob then "OK  " else "FAIL")
  putStrLn "  densified ‖H−H†‖_F < 1e-6"
  pure (okHS && okNet && okFrob)

step4 :: Ctx -> IO Bool
step4 Ctx{ctxF=f, ctxSeed=seed} = do
  putStrLn "== Step 4: Q† ∘ Q ≈ id on BulkSite (m=2, InnerSpace) =="
  let steps = NE.take 2 (lanczosTridiag f seed)
  case NE.nonEmpty steps of
    Nothing -> putStrLn "FAIL: empty Krylov" >> pure False
    Just ne | NE.length ne < 2 -> do
      putStrLn ("FAIL: only " ++ show (NE.length ne) ++ " Lanczos steps (need 2)")
      pure False
    Just ne -> do
      let qs = fmap lanczosQ ne
          q = asMap @(C 2) qs
          qDag = lanczosQDag @2 qs
          y0 = qDag $ seed
          y' = qDag $ (q $ y0)
          diff = y' ^-^ y0
          dist = sqrt (realPart (diff <.> diff))
      putStrLn ("  ‖Q† Q y − y‖ = " ++ show dist)
      let ok = dist < 1e-6
      putStrLn (if ok then "OK  " else "FAIL")
      putStrLn "  ‖Q† Q y − y‖ < 1e-6"
      pure ok

step5 :: Ctx -> IO Bool
step5 Ctx{ctxHeff=heff, ctxF=f, ctxSeed=seed} = do
  putStrLn "== Step 5: lanczosLowestQ vs groundStateDense =="
  let dim = length (basisOf @Centre)
      (eDense, vDense) = groundStateDense heff
      steps = NE.take dim (lanczosTridiag f seed)
  putStrLn ("  centre dim = " ++ show dim)
  putStrLn ("  dense λ    = " ++ show eDense)
  case NE.nonEmpty steps of
    Nothing -> putStrLn "FAIL: empty Krylov" >> pure False
    Just ne -> do
      let (eQ, vQ) = lanczosLowestQ f ne defaultLanczosTolerance
          resQ = (f $ vQ) ^-^ ((eQ :+ 0) *^ vQ)
          distQ = sqrt (realPart (resQ <.> resQ))
          resD = (f $ vDense) ^-^ ((eDense :+ 0) *^ vDense)
          distD = sqrt (realPart (resD <.> resD))
      putStrLn ("  Lanczos steps = " ++ show (NE.length ne))
      putStrLn ("  lanczos λ     = " ++ show eQ)
      putStrLn ("  ‖Heff vQ − λ vQ‖_HS = " ++ show distQ)
      putStrLn ("  ‖Heff vD − λ vD‖_HS = " ++ show distD)
      okE <- reportD "λ_Lanczos vs λ_dense" eQ eDense
      let okRes = distQ < 1e-4
      putStrLn (if okRes then "OK  " else "FAIL")
      putStrLn "  Lanczos residual < 1e-4"
      pure (okE && okRes)

runStep :: String -> IO Bool -> IO ()
runStep name act = do
  ok <- act
  if ok then putStrLn "" else do
    putStrLn ("\nSTOPPED at " ++ name)
    exitFailure

main :: IO ()
main = do
  ctx <- setup
  runStep "step 1" (step1 ctx)
  runStep "step 2" (step2 ctx)
  runStep "step 3" (step3 ctx)
  runStep "step 4" (step4 ctx)
  ok5 <- step5 ctx
  if ok5 then putStrLn "\nALL STEPS OK" >> exitSuccess
         else putStrLn "\nSTOPPED at step 5" >> exitFailure
