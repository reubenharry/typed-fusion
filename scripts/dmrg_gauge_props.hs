{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

import Test.QuickCheck (quickCheckResult)

import TensorNetwork.DMRG.Fixed
  ( prop_regaugeDepartRightPreservesMPS
  , prop_regaugeAfterRightGaugePreservesMPS
  , prop_rightGaugeMPSPreservesMPS
  , prop_siteMatrixMatchesStorage
  , prop_normalizeRightFactorizes
  , prop_moveRightPreservesMPS
  , prop_flatLeftSVDMatchesSiteMatrix
  , prop_leftCanonicalStep12
  , prop_leftCanonicalStep23
  , prop_normalizeLeftAbsorb23
  , prop_normalizeLeftAbsorb23Amplitude
  , prop_rightCanonicalStep32
  , prop_rightCanonicalStep21
  , prop_absorbRightBondMatchesKronBulk
  , prop_absorbRightBondMatchesKronLeft
  , prop_normalizeRightAbsorb32
  , prop_normalizeRightAbsorb21
  , prop_leftSvdDecomposition
  , prop_svdSplitFactorizesLeftLayout
  , prop_siteFromLeftSVDRoundtripsLeftLayout
  , prop_absorbLeftBondMatchesKronBulk
  , prop_absorbLeftBondMatchesKronRight
  , prop_siteFromSiteMatrixRoundtrip
  , prop_pairTransfer23Preserved
  )

main :: IO ()
main = do
  mapM_ run
    [ ("siteMatrix=storage", prop_siteMatrixMatchesStorage)
    , ("normalizeRight factorizes", prop_normalizeRightFactorizes)
    , ("left step 1→2", prop_leftCanonicalStep12)
    , ("left step 2→3 raw", prop_leftCanonicalStep23)
    , ("siteFromSiteMatrix roundtrip", prop_siteFromSiteMatrixRoundtrip)
    , ("absorbLeftBond kron bulk", prop_absorbLeftBondMatchesKronBulk)
    , ("absorbLeftBond kron right", prop_absorbLeftBondMatchesKronRight)
    , ("pair transfer 2–3", prop_pairTransfer23Preserved)
    , ("absorb 2–3 amplitudes", prop_normalizeLeftAbsorb23Amplitude)
    , ("normalizeLeft+absorb 2–3", prop_normalizeLeftAbsorb23)
    , ("right step 3→2", prop_rightCanonicalStep32)
    , ("right step 2→1", prop_rightCanonicalStep21)
    , ("absorbRightBond kron bulk", prop_absorbRightBondMatchesKronBulk)
    , ("absorbRightBond kron left", prop_absorbRightBondMatchesKronLeft)
    , ("normalizeRight+absorb 2–3", prop_normalizeRightAbsorb32)
    , ("normalizeRight+absorb 1–2", prop_normalizeRightAbsorb21)
    , ("leftSvd M≈UF all sites", prop_leftSvdDecomposition)
    , ("svdSplit factorizes site2", prop_svdSplitFactorizesLeftLayout)
    , ("siteFromLeftSVD roundtrip", prop_siteFromLeftSVDRoundtripsLeftLayout)
    , ("rightGauge preserves ψ", prop_rightGaugeMPSPreservesMPS)
    , ("regauge raw preserves ψ", prop_regaugeDepartRightPreservesMPS)
    , ("regauge after rightGauge", prop_regaugeAfterRightGaugePreservesMPS)
    , ("moveRight ×1", prop_moveRightPreservesMPS)
    ]
  where
    run (n, p) = quickCheckResult p >>= print . (n,)
