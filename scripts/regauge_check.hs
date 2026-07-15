{-# LANGUAGE DataKinds #-}
import Test.QuickCheck
import TensorNetwork.DMRG.Fixed (prop_regaugeDepartRightPreservesMPS, prop_moveRightLeftPreservesMPS)
import TensorNetwork.MPS.Fixed (genMPS222)

main :: IO ()
main = do
  print =<< quickCheckResult prop_regaugeDepartRightPreservesMPS
  print =<< quickCheckResult prop_moveRightLeftPreservesMPS
