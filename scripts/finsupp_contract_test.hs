{-# LANGUAGE TypeApplications #-}
import qualified Test.QuickCheck as QC
import TensorNetwork.MPS.FinSupp

main :: IO ()
main = do
  putStrLn "leftTransfer..."
  QC.quickCheck prop_leftTransferMatchesReferenceVP2 >>= print
  putStrLn "bulkTransfer..."
  QC.quickCheck prop_bulkTransferMatchesReferenceVP2 >>= print
  putStrLn "rightTransfer..."
  QC.quickCheck prop_rightTransferMatchesReferenceVP2 >>= print
  putStrLn "amplitude encode..."
  QC.quickCheck prop_amplitudeEncodeVP2 >>= print
  putStrLn "reference..."
  QC.quickCheck prop_mpsToFlatMatchesReferenceVP2 >>= print
  putStrLn "add..."
  QC.quickCheck prop_addThenFlattenVP2 >>= print
