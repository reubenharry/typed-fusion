{-# LANGUAGE DataKinds #-}
import TensorNetwork.MPS.Fixed3General
import Data.Complex (Complex)
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)
import Control.Exception

main :: IO ()
main = do
  mapM_ check [0 .. 10]
  where
    check s = do
      let mps = unGen genMPSC22 (mkQCGen s) 0
      rf <- try (evaluate (normFast mps)) :: IO (Either SomeException (Complex Double))
      rs <- try (evaluate (normSlow mps)) :: IO (Either SomeException (Complex Double))
      putStrLn $
        "seed "
          ++ show s
          ++ ": fast="
          ++ show rf
          ++ " slow="
          ++ show rs
