import Test.QuickCheck
import TensorNetwork.MPS.Fixed
  ( prop_effectiveHBulkMatchesInner
  , prop_effectiveHBulkDiagonalMatchesMPOInner
  , exampleHeffSandwich
  , fastSandwich
  )

main :: IO ()
main = do
  putStrLn "prop_effectiveHBulkMatchesInner..."
  requireQC =<< quickCheckResult prop_effectiveHBulkMatchesInner
  putStrLn "prop_effectiveHBulkDiagonalMatchesMPOInner..."
  requireQC =<< quickCheckResult prop_effectiveHBulkDiagonalMatchesMPOInner
  putStrLn $ "exampleHeffSandwich = " ++ show exampleHeffSandwich
  putStrLn $ "fastSandwich        = " ++ show fastSandwich

requireQC :: Result -> IO ()
requireQC r = case r of
  Success{} -> pure ()
  other -> fail ("QuickCheck failed: " ++ show other)
