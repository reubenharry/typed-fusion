{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExplicitNamespaces #-}

import Numeric.LinearAlgebra.Static (C, M, extract, Sized (fromList, create))
import qualified Numeric.LinearAlgebra as HM
import qualified Data.Vector.Storable as ArS
import Math.LinearMap.Category
  ( type (+>), LinearMap (..), getLinearMap )
import Math.VectorSpace.DimensionAware (unsafeFromArray, toArray)
import Numeric.LinearAlgebra.Static.COrphans ()
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Data.Complex (Complex ((:+)))
import Data.Maybe (fromJust)

main :: IO ()
main = do
  let col = ArS.fromList [3:+(-3), 1, 7:+(-7), 5] :: ArS.Vector (Complex Double)
      lm = unsafeFromArray col :: C 2 +> C 2
  putStrLn $ "unsafeFromArray col -> LinearMap =\n" ++ show (extract (getLinearMap lm))
  putStrLn $ "toArray = " ++ show (toArray lm :: ArS.Vector (Complex Double))
  let r = HM.tr (HM.reshape 2 col) :: HM.Matrix (Complex Double)
  putStrLn $ "tr.reshape 2 col =\n" ++ show r
