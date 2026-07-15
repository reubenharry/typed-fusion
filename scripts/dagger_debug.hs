{-# LANGUAGE DataKinds #-}
import Prelude hiding (($))
import Control.Arrow.Constrained (($))
import Math.LinearMap.Category (recomposeLinMap, entireBasis, SubBasis, toArray)
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C)
import qualified Data.Vector.Storable as VS
import TensorNetwork.Dagger (siteDagger, siteDaggerVec)
import TensorNetwork.Categorical.Props (genSiteMap)
import TensorNetwork.MPS.Fixed.Internal (basis)
import Test.QuickCheck (generate, Blind (..))

main :: IO ()
main = do
  Blind f <- generate (Blind <$> genSiteMap @2 @2 @2)
  let r = 0
      pullback = siteDaggerVec f (basis @2 r)
      sd = siteDagger f
      applied = sd $ basis @2 r
      imgs = [siteDaggerVec f (basis @2 j) | j <- [0, 1]]
      m = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs)
      mApplied = m $ basis @2 r
  putStrLn $ "pullback == applied (siteDagger): " ++ show (pullback == applied)
  putStrLn $ "pullback == mApplied (recompose): " ++ show (pullback == mApplied)
  putStrLn $ "toArray pullback: " ++ show (VS.toList (toArray pullback))
  putStrLn $ "toArray applied:  " ++ show (VS.toList (toArray applied))
  putStrLn $ "toArray mApplied: " ++ show (VS.toList (toArray mApplied))
