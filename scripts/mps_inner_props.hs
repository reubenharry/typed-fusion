{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

-- | QuickCheck for transfer 'mpsInner' vs physical oracle, including after
-- 'mixedCanonicalCentre3' (regression for @scripts/mps_inner_not_real.hs@).
--
--   cabal run mps-inner-props
import Test.QuickCheck
import TensorNetwork.MPS.Fixed
  ( prop_normFastMatchesSlow
  , prop_mpsInnerAfterMixedCanonical
  )

main :: IO ()
main = do
  putStrLn "prop_normFastMatchesSlow..."
  requireQC =<< quickCheckResult prop_normFastMatchesSlow
  putStrLn "prop_mpsInnerAfterMixedCanonical..."
  requireQC =<< quickCheckResult prop_mpsInnerAfterMixedCanonical

requireQC :: Result -> IO ()
requireQC r = case r of
  Success{} -> pure ()
  other -> fail ("QuickCheck failed: " ++ show other)
