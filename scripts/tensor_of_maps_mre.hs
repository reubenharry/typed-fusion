{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}

-- | Minimal slow categorical op vs raw hmatrix.
--
-- DMRG transfer / Heff wiring is full of @f ⊗^ g@. Spec (keep this API):
--
--   @(f ⊗^ g) $ (x ⊗ y) = (f $ x) ⊗ (g $ y)@
--
-- Under the hood today that is 'tensorOfMaps':
--   densify @fmap g ∘ transpose ∘ fmap f ∘ transpose@
-- with per-column @toArray@ — not Kronecker / BLAS.
--
-- This isolates @⊗^@ at TFIM-sized @(χ,p)=(3,2)@ and compares to
-- @HM.kronecker@ on densified factors, using the same fusion as
-- 'fuseBond'/'splitBond' (@toArray@ layout).
--
--   cabal run tensor-of-maps-mre
module Main where

import Prelude hiding ((.), ($))
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($))
import Control.Exception (evaluate)
import Data.Complex (Complex (..), magnitude)
import Data.Proxy (Proxy (..))
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import GHC.TypeLits (KnownNat, Nat, type (*), natVal)
import Math.LinearMap.Category
  ( LinearMap (..), getLinearMap, type (+>), type (⊗)
  )
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, Sized (extract, create))
import qualified Numeric.LinearAlgebra as HM
import Text.Printf (printf)
import System.Exit (exitFailure, exitSuccess)

import TensorNetwork.Categorical ((⊗^), fuseBond, splitBond)

type ℂ = Complex Double
type Χ = 3
type P = 2

nRep :: Int
nRep = 200

-- | @s · id :: C n +> C n@ as a densified 'LinearMap' (avoids @arr@ sampling).
scaledId :: forall (n :: Nat). KnownNat n => Double -> (C n +> C n)
scaledId s =
  case create (HM.scale (s :+ 0) (HM.ident d)) of
    Just m -> LinearMap m
    Nothing -> error "scaledId: create failed"
  where
    d = fromIntegral (natVal (Proxy @n))

-- | Frobenius-ish scalar to keep the timed thunk alive.
matNorm :: HM.Matrix ℂ -> Double
matNorm m = HM.norm_Frob (HM.cmap magnitude m)

timeLoop :: String -> Int -> (Int -> IO Double) -> IO Double
timeLoop label n act = do
  -- warmup
  _ <- act 0
  t0 <- getCurrentTime
  let go 0 acc = pure acc
      go k acc = do
        x <- act (n - k)
        go (k - 1) $! (acc + x)
  total <- go n 0
  t1 <- getCurrentTime
  let ms = 1000 * realToFrac (diffUTCTime t1 t0) :: Double
  printf "%-48s %8.3f ms total  %8.2f µs/op  (checksum=%g)\n"
    label ms (1000 * ms / fromIntegral n) total
  pure ms

-- | Categorical @f ⊗^ g@, densified to a fused @C (χ·p) +> C (χ·p)@ matrix
-- via @fuse ∘ (f⊗^g) ∘ split@ (matches production 'toArray' layout).
categoricalKron
  :: (C Χ +> C Χ) -> (C P +> C P) -> HM.Matrix ℂ
categoricalKron f g =
  let h = (f ⊗^ g) :: (C Χ ⊗ C P) +> (C Χ ⊗ C P)
      fused = fuseBond @Χ @P . h . splitBond @Χ @P :: C (Χ * P) +> C (Χ * P)
  in extract (getLinearMap fused)

-- | Raw hmatrix Kronecker on the same densified factors.
-- @HM.kronecker A B@ is the block matrix with entries @a_ij * B@.
-- With flat index @i·p + j@ (@i@ = χ factor, @j@ = p factor) this is
-- exactly @(f ⊗ g)@ on @C χ ⊗ C p@.
rawKron :: (C Χ +> C Χ) -> (C P +> C P) -> HM.Matrix ℂ
rawKron f g =
  HM.kronecker (extract (getLinearMap f)) (extract (getLinearMap g))

maxAbsDiff :: HM.Matrix ℂ -> HM.Matrix ℂ -> Double
maxAbsDiff a b =
  HM.maxElement (HM.cmap magnitude (a - b))

main :: IO ()
main = do
  let χ = fromIntegral (natVal (Proxy @Χ)) :: Int
      p = fromIntegral (natVal (Proxy @P)) :: Int
  printf "Minimal MRE: categorical (⊗^) vs HM.kronecker\n"
  printf "  χ=%d  p=%d  fused dim=%d  nRep=%d\n\n" χ p (χ * p) nRep

  -- Correctness (once): categorical must match Kronecker on fused layout.
  let f0 = scaledId @Χ 1.7
      g0 = scaledId @P (-0.3)
      cat0 = categoricalKron f0 g0
      raw0 = rawKron f0 g0
      err0 = maxAbsDiff cat0 raw0
  printf "agreement |cat - kron|_∞ = %.3g\n\n" err0
  if err0 > 1e-10
    then do
      putStrLn "FAIL: fused categorical ⊗^ does not match HM.kronecker"
      putStrLn "  (layout convention mismatch — fix comparison before trusting timings)"
      exitFailure
    else putStrLn "OK: fuse∘(f⊗^g)∘split == kronecker(f,g)\n"

  putStrLn "== timings (fresh scaled factors each iter; force densified matrix) =="
  catMs <- timeLoop "A  categorical f⊗^g → fused matrix" nRep $ \i -> do
    let s = 1 + 0.001 * fromIntegral i
        f = scaledId @Χ s
        g = scaledId @P (2 - s)
        m = categoricalKron f g
    evaluate (matNorm m)
  rawMs <- timeLoop "B  HM.kronecker (extract f, extract g)" nRep $ \i -> do
    let s = 1 + 0.001 * fromIntegral i
        f = scaledId @Χ s
        g = scaledId @P (2 - s)
        m = rawKron f g
    evaluate (matNorm m)

  -- Also time bare getLinearMap (f⊗^g) without fuse/split, in case fusion dominates.
  bareMs <- timeLoop "C  categorical getLinearMap (f⊗^g) only" nRep $ \i -> do
    let s = 1 + 0.001 * fromIntegral i
        f = scaledId @Χ s
        g = scaledId @P (2 - s)
        h = (f ⊗^ g) :: (C Χ ⊗ C P) +> (C Χ ⊗ C P)
    evaluate (matNorm (extract (getLinearMap h)))

  composeMs <- timeLoop "D  compose (f⊗^g) . (f⊗^g) categorical" nRep $ \i -> do
    let s = 1 + 0.001 * fromIntegral i
        f = scaledId @Χ s
        g = scaledId @P (2 - s)
        h = (f ⊗^ g) :: (C Χ ⊗ C P) +> (C Χ ⊗ C P)
        hh = h . h
    evaluate (matNorm (extract (getLinearMap hh)))

  gemmMs <- timeLoop "E  fused gemm: kron <> kron (raw)" nRep $ \i -> do
    let s = 1 + 0.001 * fromIntegral i
        f = scaledId @Χ s
        g = scaledId @P (2 - s)
        k = rawKron f g
        m = k HM.<> k
    evaluate (matNorm m)

  putStrLn ""
  printf "ratio A/B (cat⊗^ densify / kronecker)     = %.1fx\n" (catMs / rawMs)
  printf "ratio C/B (bare ⊗^ densify / kronecker)   = %.1fx\n" (bareMs / rawMs)
  printf "ratio D/E (cat compose / fused gemm)      = %.1fx\n" (composeMs / gemmMs)
  putStrLn ""
  putStrLn "Interpretation:"
  putStrLn "  Spec stays categorical: keep (⊗^) / tensorOfMaps API."
  putStrLn "  Fast path: implement ⊗^ for Static C by HM.kronecker (or"
  putStrLn "  equivalent) on getLinearMap payloads, then wrap LinearMap."
  putStrLn "  Same story later for composeLinear (gemm) once flat layout is safe."
  if catMs > 10 * rawMs
    then printf "\nVerdict: categorical ⊗^ is ~%.0fx slower than HM.kronecker at this size — isolated, layout-correct bottleneck.\n" (catMs / rawMs)
    else putStrLn "\nVerdict: gap smaller than expected — dig into fuse/layout next."
  exitSuccess
