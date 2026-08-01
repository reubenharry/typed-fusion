{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
import Numeric.LinearAlgebra.Static
import qualified Numeric.LinearAlgebra as H
import Math.LinearMap.Category
import Numeric.LinearAlgebra.Static.COrphans ()
import Math.VectorSpace.DimensionAware
import Data.Complex
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()

main :: IO ()
main = do
  let g = LinearMap (fromList [0, 1 :+ 1, 1, 0] :: M 2 2) :: C 2 +> C 2
      a = toArray g
      r = H.reshape 2 a
  putStrLn $ "toArray = " ++ show a
  putStrLn $ "reshape =\n" ++ show r
  putStrLn $ "tr(reshape)=\n" ++ show (H.tr r)
  putStrLn $ "tr'(reshape)=\n" ++ show (H.tr' r)
  putStrLn $ "extract g=\n" ++ show (extract (getLinearMap g))
