{-# LANGUAGE DataKinds #-}
import Test.QuickCheck (quickCheckResult)
import TensorNetwork.Categorical.Props
  ( prop_applyMatchesImages
  , prop_applyMatchesImagesTensorCodomain
  , prop_daggerSiteMatchesCoeff
  , prop_siteDaggerPullbackMatchesCoeff
  , prop_flatAdjMatchesIsoImages
  , prop_siteTensorIsoOnPullback
  , prop_composedFlatIsoApply
  , prop_siteDaggerIsoRoundtrip
  , prop_siteDaggerBasisMatchesPullback
  , prop_siteDaggerRecomposeAppliesImages
  , prop_tensorToArrayRoundtrip
  , prop_rowSliceMatchesImage
  , prop_inlineRowSumApply
  , prop_manualApplyMatchesImg
  , prop_manualRowMatchesImg
  , prop_applyLinearOnly
  , prop_arrApplyOnly
  , prop_dollarApplyOnly
  , prop_matvecMatchesStoredRow
  , prop_rowUnsafeFromArrayRoundtrip
  , prop_recomposeRowsMatchToArray
  , prop_applyTensorFlatMatchesRow
  , prop_recomposeDecomposeTensorCodomain
  , prop_recomposeAppliesImagesTensor22
  , prop_siteTensorIsoRoundtrip
  , prop_flatBasisMatchesTensor
  , prop_flatSiteApplyMatchesApplySite
  , prop_codomainIsStatic
  , prop_sliceVsExplicitDecode
  )
import TensorNetwork.MPS.Fixed3
  ( prop_transferStepMatchesMatrix
  , prop_innerMatchesReference
  , prop_innerConjugateSymmetric
  , prop_normNonNegative
  , prop_mpoTransferStepMatchesMatrix
  )

main :: IO ()
main = do
  mapM_ run
    [ ("applyTensor", prop_applyMatchesImagesTensorCodomain)
    , ("sliceVsExplicit", prop_sliceVsExplicitDecode)
    , ("manualApply", prop_manualApplyMatchesImg)
    , ("manualRow", prop_manualRowMatchesImg)
    , ("applyLinearOnly", prop_applyLinearOnly)
    , ("arrApplyOnly", prop_arrApplyOnly)
    , ("dollarApplyOnly", prop_dollarApplyOnly)
    , ("recomposeRows", prop_recomposeRowsMatchToArray)
    , ("recomposeDecomp", prop_recomposeDecomposeTensorCodomain)
    , ("flatAdj", prop_flatAdjMatchesIsoImages)
    , ("isoPullback", prop_siteTensorIsoOnPullback)
    , ("composed", prop_composedFlatIsoApply)
    , ("isoDag", prop_siteDaggerIsoRoundtrip)
    , ("applyC", prop_applyMatchesImages)
    , ("daggerBasis", prop_siteDaggerBasisMatchesPullback)
    , ("daggerSite", prop_daggerSiteMatchesCoeff)
    , ("transferStep", prop_transferStepMatchesMatrix)
    , ("inner", prop_innerMatchesReference)
    , ("conjSym", prop_innerConjugateSymmetric)
    , ("norm", prop_normNonNegative)
    , ("mpoTransfer", prop_mpoTransferStepMatchesMatrix)
    ]
  where
    run (name, prop) = do
      putStrLn name
      quickCheckResult prop >>= print
