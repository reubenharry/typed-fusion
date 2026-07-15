{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
import qualified Test.QuickCheck as QC
import TensorNetwork.MPS.FinSupp
import TensorNetwork.MPS.FinSupp.Reference (mpsToFlatReference)
import TensorNetwork.MPS.FinSupp.Physical (mpsToTensor, mpsFromPhysical)

main :: IO ()
main = do
  putStrLn "mpsToFlat vs reference vp=2..."
  QC.quickCheck prop_ref
  putStrLn "tensor round-trip vp=2..."
  QC.quickCheck prop_tensor
  where
    prop_ref m = mpsToFlat (m :: MPS 2) QC.=== mpsToFlatReference (m :: MPS 2)
    prop_tensor m =
      let t = mpsToTensor (m :: MPS 2)
      in mpsToTensor (mpsFromPhysical t) QC.=== t
