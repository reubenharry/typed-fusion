{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
import GHC.TypeLits (KnownNat)
import Numeric.LinearAlgebra.Static (C, Sized (extract, fromList))
import Math.VectorSpace.DimensionAware (toArray)
import Math.LinearMap.Category (applyLinear, getLinearFunction, (-+$>))
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import TensorNetwork.MPS.Fixed3.Internal (basis, cdim)
import TensorNetwork.MPS.LinmapStorage (linMapFromColumnImages)
import TensorNetwork.Dagger (siteDaggerVec, siteTensorIso)
import TensorNetwork.Categorical.Props (genSiteMap)
import Test.QuickCheck (generate)
import qualified Data.Vector.Storable as VS

main :: IO ()
main = do
  Just f <- generate (genSiteMap @2 @2 @2)
  let cBasis i = basis @2 i
      flatImgs =
        [ siteTensorIso @2 @2 $ siteDaggerVec f (cBasis r) | r <- [0, 1] ]
  putStrLn $ "flatImg lengths: " ++ show (map (VS.length . toArray) flatImgs)
  let flatAdj = linMapFromColumnImages @2 @4 flatImgs
  putStrLn "applying flatAdj to cBasis 0..."
  let r = getLinearFunction (applyLinear -+$> flatAdj) -+$> cBasis 0
  putStrLn $ "result length: " ++ show (VS.length (toArray r))
