module Main (main) where

import qualified Test.QuickCheck as QC
import MPS.Infinite (prop_addThenFlattenVP2, prop_addThenFlattenVP3)
import MPS.Types
  ( prop_innerMatchesFlat
  , prop_innerConjugateSymmetric
  , prop_normNonNegative
  , prop_mpoInnerMatchesFlat
  , prop_mpoApplyMPSMatchesFlat
  , prop_identityMPOMatchesInner
  )

requireQC :: QC.Result -> IO ()
requireQC (QC.Success{}) = pure ()
requireQC r = fail ("QuickCheck property failed: " ++ show r)

main :: IO ()
main = do
  putStrLn "MPS addition commutes with flattening (vp = 2)..."
  requireQC =<< QC.quickCheckResult prop_addThenFlattenVP2
  putStrLn "MPS addition commutes with flattening (vp = 3)..."
  requireQC =<< QC.quickCheckResult prop_addThenFlattenVP3
  putStrLn "MPS inner product matches flattened overlap..."
  requireQC =<< QC.quickCheckResult prop_innerMatchesFlat
  putStrLn "MPS inner product is conjugate-symmetric..."
  requireQC =<< QC.quickCheckResult prop_innerConjugateSymmetric
  putStrLn "MPS norm-squared is real and non-negative..."
  requireQC =<< QC.quickCheckResult prop_normNonNegative
  putStrLn "MPS-MPO-MPS contraction matches flattened operator..."
  requireQC =<< QC.quickCheckResult prop_mpoInnerMatchesFlat
  putStrLn "MPO application in MPS form matches flattened operator..."
  requireQC =<< QC.quickCheckResult prop_mpoApplyMPSMatchesFlat
  putStrLn "Identity MPO matches MPS inner product..."
  requireQC =<< QC.quickCheckResult prop_identityMPOMatchesInner
  putStrLn "All OK."
