module Main (main) where

import qualified Test.QuickCheck as QC
import Infinite (prop_addThenFlattenVP2, prop_addThenFlattenVP3)

requireQC :: QC.Result -> IO ()
requireQC (QC.Success{}) = pure ()
requireQC r = fail ("QuickCheck property failed: " ++ show r)

main :: IO ()
main = do
  putStrLn "MPS addition commutes with flattening (vp = 2)..."
  requireQC =<< QC.quickCheckResult prop_addThenFlattenVP2
  putStrLn "MPS addition commutes with flattening (vp = 3)..."
  requireQC =<< QC.quickCheckResult prop_addThenFlattenVP3
  putStrLn "All OK."
