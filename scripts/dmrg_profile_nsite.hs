{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE NoStarIsType #-}

-- | Profile one zipper sweep on N-site TFIM, broken into:
--   mixedCanonicalLeft, env rebuild, Lanczos solve, gauge shift, energy.
--
--   cabal run dmrg-profile-nsite
--
-- Bulk length @q@ ⇒ physical sites @N = q + 2@. Default q=6 → N=8.
module Main where

import Prelude hiding (($))
import Control.Arrow.Constrained (($))
import Control.Exception (evaluate)
import Control.Lens ((^.), (^?), (&), (.~), (%~))
import Control.Lens.At (Ixed (ix))
import Data.Complex (realPart)
import Data.Finite (getFinite)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import Data.VectorSpace (InnerSpace ((<.>)))
import GHC.TypeNats (natVal)
import Math.LinearMap.Category (getLinearMap)
import Numeric.LinearAlgebra.Static (C)
import Text.Printf (printf)

import Lanczos (groundStateLanczos)
import TensorNetwork.DMRG.Fixed
  ( centreDimBulk, centreDimLeft, centreDimRight
  , energy, heffBulk, heffLeft, heffRight
  , productMPS, sweep, tfimMPO
  )
import TensorNetwork.MPS.General
  ( CenterPos (..)
  , FullNorm
  , MPS
  , MPO
  , hermitianNorm
  , mixedCanonicalLeft
  , mpsBulk, mpsLeft, mpsRight
  , shiftGaugeLeft, shiftGaugeRight
  )

-- | Bulk length → N = q+2 physical sites.
type BulkSites = 6

data Acc = Acc
  { accEnvMs :: !Double
  , accSolveMs :: !Double
  , accGaugeMs :: !Double
  , accEnergyMs :: !Double
  , accSites :: !Int
  }

zeroAcc :: Acc
zeroAcc = Acc 0 0 0 0 0

timed :: IO a -> IO (Double, a)
timed act = do
  t0 <- getCurrentTime
  a <- act
  t1 <- getCurrentTime
  pure (1000 * realToFrac (diffUTCTime t1 t0), a)

posLabel :: CenterPos BulkSites -> String
posLabel CenterLeft = "L"
posLabel CenterRight = "R"
posLabel (CenterBulk j) = "B" ++ show (getFinite j)

forceMPS :: MPS (C 3) (C 2) BulkSites -> IO ()
forceMPS mps = do
  _ <- evaluate (getLinearMap (mps ^. mpsLeft))
  _ <- evaluate (getLinearMap (mps ^. mpsRight))
  let q = fromIntegral (natVal (Proxy @BulkSites)) :: Int
  mapM_
    ( \j ->
        case mps ^? mpsBulk . ix j of
          Just s -> evaluate (getLinearMap s) >> pure ()
          Nothing -> error "forceMPS: missing bulk"
    )
    [0 .. q - 1]

-- | Env cost = construct Heff + first matvec (builds L/R from scratch).
--   Solve cost = Lanczos on that already-forced Heff.
profileSite
  :: FullNorm (C 3) -> FullNorm (C 2)
  -> CenterPos BulkSites
  -> MPO (C 3) BulkSites (C 2) (C 2)
  -> MPS (C 3) (C 2) BulkSites
  -> IO (Double, Double, Double, MPS (C 3) (C 2) BulkSites)
profileSite nb np pos mpo mps =
  case pos of
    CenterLeft -> do
      let seed = mps ^. mpsLeft
      (envMs, heff) <- timed $ do
        let h = heffLeft nb np mps mpo
        _ <- evaluate (realPart (seed <.> (h $ seed)))
        pure h
      (solveMs, (lam, s)) <- timed $ do
        let out = groundStateLanczos (centreDimLeft @3 @2) seed heff
        _ <- evaluate (fst out)
        _ <- evaluate (getLinearMap (snd out))
        pure out
      pure (envMs, solveMs, lam, mps & mpsLeft .~ s)
    CenterRight -> do
      let seed = mps ^. mpsRight
      (envMs, heff) <- timed $ do
        let h = heffRight nb np mps mpo
        _ <- evaluate (realPart (seed <.> (h $ seed)))
        pure h
      (solveMs, (lam, s)) <- timed $ do
        let out = groundStateLanczos (centreDimRight @3 @2) seed heff
        _ <- evaluate (fst out)
        _ <- evaluate (getLinearMap (snd out))
        pure out
      pure (envMs, solveMs, lam, mps & mpsRight .~ s)
    CenterBulk j -> do
      let ji = fromIntegral (getFinite j)
          seed = fromMaybe (error "bulk") (mps ^? mpsBulk . ix ji)
      (envMs, heff) <- timed $ do
        let h = heffBulk nb np ji mps mpo
        _ <- evaluate (realPart (seed <.> (h $ seed)))
        pure h
      (solveMs, (lam, s)) <- timed $ do
        let out = groundStateLanczos (centreDimBulk @3 @2) seed heff
        _ <- evaluate (fst out)
        _ <- evaluate (getLinearMap (snd out))
        pure out
      pure (envMs, solveMs, lam, mps & mpsBulk %~ ix ji .~ s)

stepRight
  :: FullNorm (C 3) -> FullNorm (C 2)
  -> MPO (C 3) BulkSites (C 2) (C 2)
  -> CenterPos BulkSites
  -> MPS (C 3) (C 2) BulkSites
  -> Acc
  -> IO (CenterPos BulkSites, MPS (C 3) (C 2) BulkSites, Acc)
stepRight nb np mpo pos mps acc = do
  (envMs, solveMs, lam, mps1) <- profileSite nb np pos mpo mps
  (energyMs, e) <- timed $ evaluate (energy nb np mpo mps1)
  printf "  %-4s  env=%7.1f  solve=%7.1f  energy=%7.1f  λ=% .6f  E=% .6f\n"
    (posLabel pos) envMs solveMs energyMs lam e
  let acc' =
        acc
          { accEnvMs = accEnvMs acc + envMs
          , accSolveMs = accSolveMs acc + solveMs
          , accEnergyMs = accEnergyMs acc + energyMs
          , accSites = accSites acc + 1
          }
  case pos of
    CenterRight -> pure (pos, mps1, acc')
    _ -> do
      (gaugeMs, (pos', mps2)) <- timed $ do
        let out = shiftGaugeRight @3 @2 @BulkSites pos mps1
        forceMPS (snd out) >> pure out
      printf "        gauge→%-4s %7.1f ms\n" (posLabel pos') gaugeMs
      pure (pos', mps2, acc' { accGaugeMs = accGaugeMs acc' + gaugeMs })

stepLeft
  :: FullNorm (C 3) -> FullNorm (C 2)
  -> MPO (C 3) BulkSites (C 2) (C 2)
  -> CenterPos BulkSites
  -> MPS (C 3) (C 2) BulkSites
  -> Acc
  -> IO (CenterPos BulkSites, MPS (C 3) (C 2) BulkSites, Acc)
stepLeft nb np mpo pos mps acc = do
  (envMs, solveMs, lam, mps1) <- profileSite nb np pos mpo mps
  (energyMs, e) <- timed $ evaluate (energy nb np mpo mps1)
  printf "  %-4s  env=%7.1f  solve=%7.1f  energy=%7.1f  λ=% .6f  E=% .6f\n"
    (posLabel pos) envMs solveMs energyMs lam e
  let acc' =
        acc
          { accEnvMs = accEnvMs acc + envMs
          , accSolveMs = accSolveMs acc + solveMs
          , accEnergyMs = accEnergyMs acc + energyMs
          , accSites = accSites acc + 1
          }
  case pos of
    CenterLeft -> pure (pos, mps1, acc')
    _ -> do
      (gaugeMs, (pos', mps2)) <- timed $ do
        let out = shiftGaugeLeft @3 @2 @BulkSites pos mps1
        forceMPS (snd out) >> pure out
      printf "        gauge→%-4s %7.1f ms\n" (posLabel pos') gaugeMs
      pure (pos', mps2, acc' { accGaugeMs = accGaugeMs acc' + gaugeMs })

sweepRight
  :: FullNorm (C 3) -> FullNorm (C 2)
  -> MPO (C 3) BulkSites (C 2) (C 2)
  -> CenterPos BulkSites
  -> MPS (C 3) (C 2) BulkSites
  -> Acc
  -> IO (MPS (C 3) (C 2) BulkSites, Acc)
sweepRight nb np mpo pos mps acc = do
  (pos', mps', acc') <- stepRight nb np mpo pos mps acc
  case pos of
    CenterRight -> pure (mps', acc')
    _ -> sweepRight nb np mpo pos' mps' acc'

-- After right solve, shift left once then continue (mirrors solveAllSites).
sweepLeftBack
  :: FullNorm (C 3) -> FullNorm (C 2)
  -> MPO (C 3) BulkSites (C 2) (C 2)
  -> MPS (C 3) (C 2) BulkSites
  -> Acc
  -> IO (MPS (C 3) (C 2) BulkSites, Acc)
sweepLeftBack nb np mpo mpsAtRight acc = do
  (gaugeMs, (pos0, mps0)) <- timed $ do
    let out = shiftGaugeLeft @3 @2 @BulkSites CenterRight mpsAtRight
    forceMPS (snd out) >> pure out
  printf "        gauge→%-4s %7.1f ms  (start leftward)\n" (posLabel pos0) gaugeMs
  go pos0 mps0 (acc { accGaugeMs = accGaugeMs acc + gaugeMs })
  where
    go pos mps a = do
      (pos', mps', a') <- stepLeft nb np mpo pos mps a
      case pos of
        CenterLeft -> pure (mps', a')
        _ -> go pos' mps' a'

printAcc :: String -> Double -> Acc -> IO ()
printAcc title initMs acc = do
  let total =
        initMs + accEnvMs acc + accSolveMs acc + accGaugeMs acc + accEnergyMs acc
      pct x = if total <= 0 then 0 else 100 * x / total
  putStrLn ""
  putStrLn title
  printf "  sites solved:     %d\n" (accSites acc)
  printf "  mixedCanonical: %8.1f ms  (%5.1f%%)\n" initMs (pct initMs)
  printf "  env rebuild:    %8.1f ms  (%5.1f%%)\n" (accEnvMs acc) (pct (accEnvMs acc))
  printf "  Lanczos solve:  %8.1f ms  (%5.1f%%)\n" (accSolveMs acc) (pct (accSolveMs acc))
  printf "  gauge shift:    %8.1f ms  (%5.1f%%)\n" (accGaugeMs acc) (pct (accGaugeMs acc))
  printf "  energy():       %8.1f ms  (%5.1f%%)\n" (accEnergyMs acc) (pct (accEnergyMs acc))
  printf "  sum (profiled): %8.1f ms\n" total

main :: IO ()
main = do
  let nb = hermitianNorm :: FullNorm (C 3)
      np = hermitianNorm :: FullNorm (C 2)
      q = fromIntegral (natVal (Proxy @BulkSites)) :: Int
      nSites = q + 2
      mpo = tfimMPO @BulkSites 1.0 0.7
      psi0 = productMPS @BulkSites
  printf "TFIM profile: N=%d physical (bulk q=%d), χ=3, p=2\n" nSites q
  printf "One full L→R→L sweep with per-site energy (same as solveAllSites).\n\n"

  putStrLn "== initial gauge =="
  (initMs, psiL) <- timed $ do
    let p = mixedCanonicalLeft @3 @2 @BulkSites psi0
    forceMPS p >> pure p
  printf "  mixedCanonicalLeft  %8.1f ms\n" initMs

  putStrLn "\n== left → right =="
  (mpsR, accR) <- sweepRight nb np mpo CenterLeft psiL zeroAcc

  putStrLn "\n== right → left =="
  (mpsFinal, acc) <- sweepLeftBack nb np mpo mpsR accR

  printAcc "== totals (instrumented sweep) ==" initMs acc

  putStrLn "\n== production sweep wall-clock (for comparison) =="
  (sweepMs, (_, hist)) <- timed $ do
    let out = sweep @3 @2 @BulkSites mpo psi0
    _ <- evaluate (last (snd out))
    pure out
  printf "  sweep ×1  %8.1f ms   hist len=%d  E_final=% .6f\n"
    sweepMs (length hist) (last hist)

  forceMPS mpsFinal
