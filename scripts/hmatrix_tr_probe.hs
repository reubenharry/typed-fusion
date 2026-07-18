import qualified Numeric.LinearAlgebra as H
import Data.Complex

main :: IO ()
main = do
  let m = (2 H.>< 2) [1, 2:+1, 3, 4] :: H.Matrix (Complex Double)
  putStrLn $ "m =\n" ++ show m
  putStrLn $ "tr m =\n" ++ show (H.tr m)
  putStrLn $ "tr' m =\n" ++ show (H.tr' m)
  putStrLn $ "cmap conjugate (tr' m) =\n" ++ show (H.cmap conjugate (H.tr' m))
