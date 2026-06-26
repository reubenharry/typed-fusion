import qualified Test.QuickCheck as QC
import TensorNetwork.MPS.FinSupp3

requireQC :: QC.Result -> IO ()
requireQC (QC.Success{}) = pure ()
requireQC r = fail ("QuickCheck property failed: " ++ show r)

main :: IO ()
main = do
  putStrLn "FinSupp add/flatten vp=2..."
  requireQC =<< QC.quickCheckResult prop_addThenFlattenVP2
  putStrLn "FinSupp add/flatten vp=3..."
  requireQC =<< QC.quickCheckResult prop_addThenFlattenVP3
  putStrLn "FinSupp basis MPS vp=2..."
  requireQC =<< QC.quickCheckResult prop_basisMPSMatchesPhysicalVP2
  putStrLn "FinSupp basis MPS vp=3..."
  requireQC =<< QC.quickCheckResult prop_basisMPSMatchesPhysicalVP3
  putStrLn "FinSupp decompose' vp=2..."
  requireQC =<< QC.quickCheckResult prop_decomposePrimeMatchesPhysicalVP2
  putStrLn "FinSupp decompose' vp=3..."
  requireQC =<< QC.quickCheckResult prop_decomposePrimeMatchesPhysicalVP3
  putStrLn "FinSupp mpsToFlat vs reference vp=2..."
  requireQC =<< QC.quickCheckResult prop_mpsToFlatMatchesReferenceVP2
  putStrLn "FinSupp amplitude encode vp=2..."
  requireQC =<< QC.quickCheckResult prop_amplitudeEncodeVP2
  putStrLn "FinSupp tensor encode round-trip vp=2..."
  requireQC =<< QC.quickCheckResult prop_tensorEncodeVP2
  putStrLn "FinSupp canonicalMPS vp=2..."
  requireQC =<< QC.quickCheckResult prop_physicalRecomposeVP2
  putStrLn "FinSupp canonicalMPS vp=3..."
  requireQC =<< QC.quickCheckResult prop_physicalRecomposeVP3
  putStrLn "FinSupp mpsFromFlat vp=2..."
  requireQC =<< QC.quickCheckResult prop_mpsFromFlatRoundTripVP2
  putStrLn "FinSupp mpsFromFlat vp=3..."
  requireQC =<< QC.quickCheckResult prop_mpsFromFlatRoundTripVP3
  putStrLn "FinSupp mpsToFlat reference vp=2..."
  requireQC =<< QC.quickCheckResult prop_mpsToFlatMatchesReferenceVP2
  putStrLn "FinSupp mpsToFlat reference vp=3..."
  requireQC =<< QC.quickCheckResult prop_mpsToFlatMatchesReferenceVP3
  putStrLn "FinSupp leftTransfer vp=2..."
  requireQC =<< QC.quickCheckResult prop_leftTransferMatchesReferenceVP2
  putStrLn "FinSupp bulkTransfer vp=2..."
  requireQC =<< QC.quickCheckResult prop_bulkTransferMatchesReferenceVP2
  putStrLn "FinSupp rightTransfer vp=2..."
  requireQC =<< QC.quickCheckResult prop_rightTransferMatchesReferenceVP2
  putStrLn "FinSupp mpoApply vp=2..."
  requireQC =<< QC.quickCheckResult prop_mpoApplyFlatMatchesReferenceVP2
  putStrLn "All FinSupp smoke tests passed."
