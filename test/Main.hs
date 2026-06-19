{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
module Main (main) where

import qualified Test.QuickCheck as QC
import TensorNetwork.MPS.FinSupp3
  ( prop_addThenFlattenVP2
  , prop_addThenFlattenVP3
  , prop_basisMPSMatchesPhysicalVP2
  , prop_basisMPSMatchesPhysicalVP3
  , prop_decomposePrimeMatchesPhysicalVP2
  , prop_decomposePrimeMatchesPhysicalVP3
  , prop_physicalRecomposeVP2
  , prop_physicalRecomposeVP3
  , prop_mpsFromFlatRoundTripVP2
  , prop_mpsFromFlatRoundTripVP3
  )
import TensorNetwork.Categorical.Props
  ( prop_applyMatchesImages
  , prop_applyMatchesImagesTensorCodomain
  , prop_tensorOfMapsActsFactorwise
  , prop_swapMapMatchesTranspose
  , prop_assocRoundTrip
  , prop_lassocMatchesNesting
  , prop_lunitClosesBoundary
  , prop_runitClosesBoundary
  , prop_unitRoundTrip
  , prop_conjugateMapMatchesEntrywise
  , prop_conjugateSiteMatchesCoeff
  , prop_daggerCnMatchesConjTranspose
  , prop_daggerSiteMatchesCoeff
  )
import TensorNetwork.MPS.Fixed3
  ( prop_applySiteMatchesCoeff
  , prop_applyOpSiteMatchesCoeff
  , prop_conjSiteMatchesCoeff
  , prop_transferStepMatchesMatrix
  , prop_mpsToFlatMatchesReference
  , prop_innerMatchesFlat
  , prop_innerMatchesReference
  , prop_innerConjugateSymmetric
  , prop_normNonNegative
  , prop_mpoTransferStepMatchesMatrix
  , prop_mpsMPOInnerMatchesReference
  , prop_mpoInnerMatchesFlat
  , prop_mpoApplyMPSMatchesFlat
  , prop_identityMPOMatchesInner
  , prop_mpsFromFlatRoundTripP2
  , prop_mpsFromFlatOnRandomFlatP2
  , prop_mpsFromFlatRoundTripP3
  , prop_canonicalMPSRoundTripP2
  , prop_canonicalMPSRoundTripP3
  )
import GHC.TypeLits (type (*))
import TensorNetwork.DMRG.Fixed3
  ( prop_effectiveHMatchesInner
  , prop_effectiveHHermitian
  , prop_flatLeftSVDMatchesSiteMatrix
  , prop_dmrgGroundEnergyMatchesDense
  , prop_eigenMatchesDenseC4
  , tfimMPO
  , dmrg
  , sweep
  , energy
  , denseGroundEnergy
  , seededMPS222
  )

requireQC :: QC.Result -> IO ()
requireQC (QC.Success{}) = pure ()
requireQC r = fail ("QuickCheck property failed: " ++ show r)

requireClose :: String -> Double -> Double -> Double -> IO ()
requireClose what tol expected actual
  | abs (expected - actual) <= tol = pure ()
  | otherwise =
      fail (what ++ ": expected " ++ show expected ++ ", got " ++ show actual)

-- | DMRG on the 3-site TFIM reproduces the dense @C 8@ ground energy, and a
-- sweep never raises the energy of the previous sweep.
checkDMRG :: Double -> Double -> IO ()
checkDMRG j h = do
  let mpo = tfimMPO j h
      psi0 = seededMPS222 42
      (e1, psi1) = sweep mpo psi0
      (e, _) = dmrg 10 1e-12 mpo sweep psi0
      eDense = denseGroundEnergy mpo
  requireClose "sweep energy vs Rayleigh quotient" 1e-9 (energy mpo psi1) e1
  requireClose "DMRG vs dense ground energy" 1e-9 eDense e
  if e1 >= eDense - 1e-9
    then pure ()
    else fail "sweep energy below dense ground energy (impossible)"

main :: IO ()
main = do
  putStrLn "Recomposed map applies basis to its images..."
  requireQC =<< QC.quickCheckResult prop_applyMatchesImages
  putStrLn "... also with tensor codomain..."
  requireQC =<< QC.quickCheckResult prop_applyMatchesImagesTensorCodomain
  putStrLn "tensorOfMaps acts factorwise..."
  requireQC =<< QC.quickCheckResult prop_tensorOfMapsActsFactorwise
  putStrLn "swapMap matches transposeTensor..."
  requireQC =<< QC.quickCheckResult prop_swapMapMatchesTranspose
  putStrLn "lassocMap matches nesting..."
  requireQC =<< QC.quickCheckResult prop_lassocMatchesNesting
  putStrLn "Associators round-trip..."
  requireQC =<< QC.quickCheckResult prop_assocRoundTrip
  putStrLn "lunit closes the boundary..."
  requireQC =<< QC.quickCheckResult prop_lunitClosesBoundary
  putStrLn "runit closes the boundary..."
  requireQC =<< QC.quickCheckResult prop_runitClosesBoundary
  putStrLn "Unitors round-trip..."
  requireQC =<< QC.quickCheckResult prop_unitRoundTrip
  putStrLn "conjugateMap conjugates entrywise (C n +> C m)..."
  requireQC =<< QC.quickCheckResult prop_conjugateMapMatchesEntrywise
  putStrLn "conjugateMap respects site layout (vectorConjugate regression)..."
  requireQC =<< QC.quickCheckResult prop_conjugateSiteMatchesCoeff
  putStrLn "dagger is the conjugate transpose (C n +> C m)..."
  requireQC =<< QC.quickCheckResult prop_daggerCnMatchesConjTranspose
  putStrLn "Site dagger matches coefficient oracle..."
  requireQC =<< QC.quickCheckResult prop_daggerSiteMatchesCoeff
  putStrLn "Categorical site apply matches coefficient oracle..."
  requireQC =<< QC.quickCheckResult prop_applySiteMatchesCoeff
  putStrLn "Categorical MPO site apply matches coefficient oracle..."
  requireQC =<< QC.quickCheckResult prop_applyOpSiteMatchesCoeff
  putStrLn "MPS addition commutes with flattening (vp = 2)..."
  requireQC =<< QC.quickCheckResult prop_addThenFlattenVP2
  putStrLn "MPS addition commutes with flattening (vp = 3)..."
  requireQC =<< QC.quickCheckResult prop_addThenFlattenVP3
  putStrLn "MPS physical basis vectors match Physical3 basis (vp = 2)..."
  requireQC =<< QC.quickCheckResult prop_basisMPSMatchesPhysicalVP2
  putStrLn "MPS physical basis vectors match Physical3 basis (vp = 3)..."
  requireQC =<< QC.quickCheckResult prop_basisMPSMatchesPhysicalVP3
  putStrLn "MPS decompose' matches Physical3 decompose' (vp = 2)..."
  requireQC =<< QC.quickCheckResult prop_decomposePrimeMatchesPhysicalVP2
  putStrLn "MPS decompose' matches Physical3 decompose' (vp = 3)..."
  requireQC =<< QC.quickCheckResult prop_decomposePrimeMatchesPhysicalVP3
  putStrLn "canonicalMPS round-trips on physical space (vp = 2)..."
  requireQC =<< QC.quickCheckResult prop_physicalRecomposeVP2
  putStrLn "canonicalMPS round-trips on physical space (vp = 3)..."
  requireQC =<< QC.quickCheckResult prop_physicalRecomposeVP3
  putStrLn "mpsFromFlat round-trips on physical space (vp = 2)..."
  requireQC =<< QC.quickCheckResult prop_mpsFromFlatRoundTripVP2
  putStrLn "mpsFromFlat round-trips on physical space (vp = 3)..."
  requireQC =<< QC.quickCheckResult prop_mpsFromFlatRoundTripVP3
  putStrLn "Transfer step matches explicit matrix formula..."
  requireQC =<< QC.quickCheckResult prop_transferStepMatchesMatrix
  putStrLn "conjugateSite matches entry-wise matrix conjugation..."
  requireQC =<< QC.quickCheckResult prop_conjSiteMatchesCoeff
  putStrLn "Categorical mpsToFlat matches basis-sum reference..."
  requireQC =<< QC.quickCheckResult prop_mpsToFlatMatchesReference
  putStrLn "MPS inner product matches flattened overlap..."
  requireQC =<< QC.quickCheckResult prop_innerMatchesFlat
  putStrLn "MPS inner product matches basis reference..."
  requireQC =<< QC.quickCheckResult prop_innerMatchesReference
  putStrLn "MPS inner product is conjugate-symmetric..."
  requireQC =<< QC.quickCheckResult prop_innerConjugateSymmetric
  putStrLn "MPS norm-squared is real and non-negative..."
  requireQC =<< QC.quickCheckResult prop_normNonNegative
  putStrLn "MPO transfer step matches explicit matrix formula..."
  requireQC =<< QC.quickCheckResult prop_mpoTransferStepMatchesMatrix
  putStrLn "Categorical MPS-MPO-MPS inner matches basis reference..."
  requireQC =<< QC.quickCheckResult prop_mpsMPOInnerMatchesReference
  putStrLn "MPS-MPO-MPS contraction matches flattened operator..."
  requireQC =<< QC.quickCheckResult prop_mpoInnerMatchesFlat
  putStrLn "MPO application in MPS form matches flattened operator..."
  requireQC =<< QC.quickCheckResult prop_mpoApplyMPSMatchesFlat
  putStrLn "Identity MPO matches MPS inner product..."
  requireQC =<< QC.quickCheckResult prop_identityMPOMatchesInner
  putStrLn "Fixed3 SVD mpsFromFlat round-trips (p = 2)..."
  requireQC =<< QC.quickCheckResult prop_mpsFromFlatRoundTripP2
  putStrLn "Fixed3 SVD mpsFromFlat on random flat C^8 (p = 2)..."
  requireQC =<< QC.quickCheckResult prop_mpsFromFlatOnRandomFlatP2
  putStrLn "Fixed3 SVD mpsFromFlat round-trips (p = 3)..."
  requireQC =<< QC.quickCheckResult prop_mpsFromFlatRoundTripP3
  putStrLn "Fixed3 SVD canonicalMPS round-trips (p = 2)..."
  requireQC =<< QC.quickCheckResult prop_canonicalMPSRoundTripP2
  putStrLn "Fixed3 SVD canonicalMPS round-trips (p = 3)..."
  requireQC =<< QC.quickCheckResult prop_canonicalMPSRoundTripP3
  putStrLn "<y, Heff x> matches the full network contraction..."
  requireQC =<< QC.quickCheckResult prop_effectiveHMatchesInner
  putStrLn "Effective Hamiltonian is Hermitian (TFIM)..."
  requireQC =<< QC.quickCheckResult prop_effectiveHHermitian
  putStrLn "Flat left-SVD layout matches siteMatrix oracle..."
  requireQC =<< QC.quickCheckResult prop_flatLeftSVDMatchesSiteMatrix
  putStrLn "DMRG ground energy matches dense oracle (100 seeds)..."
  requireQC =<< QC.quickCheckResult prop_dmrgGroundEnergyMatchesDense
  putStrLn "eigen path matches dense oracle on C 4..."
  requireQC =<< QC.quickCheckResult prop_eigenMatchesDenseC4
  putStrLn "DMRG matches dense ground energy (J=1, h=0.7)..."
  checkDMRG 1 0.7
  putStrLn "DMRG matches dense ground energy (J=0.5, h=1.3)..."
  checkDMRG 0.5 1.3
  putStrLn "All OK."
