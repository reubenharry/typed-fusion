{-# LANGUAGE DataKinds #-}
import Test.QuickCheck
import TensorNetwork.DMRG.Fixed3 (prop_regaugeDepartRightPreservesMPS, prop_moveRightLeftPreservesMPS)
import TensorNetwork.MPS.Fixed3 (genMPS222)

main :: IO ()
main = do
  print =<< quickCheckResult prop_regaugeDepartRightPreservesMPS
  print =<< quickCheckResult prop_moveRightLeftPreservesMPS
