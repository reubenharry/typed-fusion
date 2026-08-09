{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
module Main (main) where

import qualified Test.QuickCheck as QC
import TensorNetwork.MPS.Fixed
  ( prop_normFastMatchesSlow
  , prop_mpsInnerAfterMixedCanonical
  , prop_effectiveHBulkMatchesInner
  , prop_effectiveHBulkDiagonalMatchesMPOInner
  , prop_shiftGaugePreservesPhysical
  , prop_shiftGaugeRoundTrip
  , prop_shiftGaugeMatchesMixedCanonical3
  , prop_shiftGaugePreservesInnerQ2
  )
import TensorNetwork.LieGroup (prop_haarUnitary)
import TensorNetwork.Bundle (prop_regaugePreservesPhysical)
import TensorNetwork.DMRG.Fixed
  ( prop_dmrgConvergesFromRandomMPS
  , prop_dmrgSweepNonIncreasingQ2
  )
import Lanczos (prop_lanczosQDagEmbedIdC2)

requireQC :: QC.Result -> IO ()
requireQC (QC.Success{}) = pure ()
requireQC r = fail ("QuickCheck property failed: " ++ show r)

main :: IO ()
main = do
  putStrLn "Lanczos Q†Q ≈ id on C 2..."
  requireQC =<< QC.quickCheckResult prop_lanczosQDagEmbedIdC2
  putStrLn "Haar U(3) unitarity..."
  requireQC =<< QC.quickCheckResult prop_haarUnitary
  putStrLn "bond regauge preserves physical..."
  requireQC =<< QC.quickCheckResult prop_regaugePreservesPhysical
  putStrLn "normFast matches normSlow..."
  requireQC =<< QC.quickCheckResult prop_normFastMatchesSlow
  putStrLn "mpsInner after mixedCanonical*3..."
  requireQC =<< QC.quickCheckResult prop_mpsInnerAfterMixedCanonical
  putStrLn "effectiveHBulk matches network inner..."
  requireQC =<< QC.quickCheckResult prop_effectiveHBulkMatchesInner
  putStrLn "effectiveHBulk diagonal matches mpsMPOInner..."
  requireQC =<< QC.quickCheckResult prop_effectiveHBulkDiagonalMatchesMPOInner
  putStrLn "shiftGauge preserves physical (q=1)..."
  requireQC =<< QC.quickCheckResult prop_shiftGaugePreservesPhysical
  putStrLn "shiftGauge round-trip (q=1)..."
  requireQC =<< QC.quickCheckResult prop_shiftGaugeRoundTrip
  putStrLn "shiftGauge matches mixedCanonical*3 endpoints..."
  requireQC =<< QC.quickCheckResult prop_shiftGaugeMatchesMixedCanonical3
  putStrLn "shiftGauge preserves mpsInner (q=2)..."
  requireQC =<< QC.quickCheckResult prop_shiftGaugePreservesInnerQ2
  putStrLn "DMRG converges from random MPS..."
  requireQC =<< QC.quickCheckResult prop_dmrgConvergesFromRandomMPS
  putStrLn "DMRG zipper sweep nonincreasing (q=2)..."
  requireQC =<< QC.quickCheckResult prop_dmrgSweepNonIncreasingQ2
  putStrLn "All OK."
