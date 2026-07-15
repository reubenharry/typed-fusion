{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
import TensorNetwork.MPS.Fixed
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)
import Numeric.LinearAlgebra.Static (unwrap)
import qualified Data.Vector.Storable as VS
import Data.Complex (magnitude)

main :: IO ()
main = do
  mapM_ check [0 .. 20]
  where
    check s = do
      let m = unGen genMPS222 (mkQCGen s) 30
          flat0 = mpsToFlat m
          flat1 = mpsToFlat (mpsFromFlat @2 @2 @2 flat0)
          err =
            maximum $
              map magnitude $
                VS.toList (VS.zipWith (-) (unwrap flat1) (unwrap flat0))
      putStrLn $ "seed " ++ show s ++ ": max err = " ++ show err
