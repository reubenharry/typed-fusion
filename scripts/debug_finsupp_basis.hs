{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
import Data.Finite (getFinite)
import Math.LinearMap.Category (type (⊗), (⊗))
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.VectorSpace.DimensionAware (toArray)
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (Sized (unwrap))
import GHC.TypeLits ()
import qualified Data.Vector.Storable as VS
import TensorNetwork.MPS.FinSupp.Internal (basisCvp, Physical3)
import TensorNetwork.MPS.FinSupp.Physical (productMPSAtIndices, mpsToFlat, physicalToFlat)
import TensorNetwork.MPS.FinSupp.Reference (amplitude, flatIndex3)

flatIdx :: VS.Vector a -> Int
flatIdx v = head [ i | i <- [0 .. VS.length v - 1], v VS.! i /= 0 ]

main :: IO ()
main = do
  let phys = basisCvp @2 1 ⊗ (basisCvp @2 0 ⊗ basisCvp @2 1)
      arr = toArray phys
  putStrLn $ "toArray(basis 1⊗(0⊗1)) at " ++ show (flatIdx arr)
  putStrLn $ "flatIndex3(1,0,1) = " ++ show (flatIndex3 2 1 0 1)
  let mps = productMPSAtIndices 1 0 1
  putStrLn $ "amp(1,0,1) = " ++ show (amplitude mps 1 0 1)
  putStrLn $ "amp(1,1,0) = " ++ show (amplitude mps 1 1 0)
  putStrLn $ "product mpsToFlat at " ++ show (flatIdx (unwrap (mpsToFlat mps)))
  putStrLn $ "physicalToFlat at " ++ show (flatIdx (unwrap (physicalToFlat phys)))
