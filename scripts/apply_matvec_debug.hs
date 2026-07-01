{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
import Data.Complex (Complex ((:+)))
import Control.Arrow.Constrained (($), arr)
import Math.LinearMap.Category
  ( type (+>), type (⊗), (⊗), recomposeLinMap, entireBasis, SubBasis
  , applyLinear, (-+$>), getLinearMap, getLinearFunction )
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, extract, Sized (fromList))
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import Data.VectorSpace (VectorSpace ((*^)), sumV)
import qualified Numeric.LinearAlgebra.HMatrix as HM
import qualified Data.Vector.Storable as VS
import Numeric.LinearAlgebra.Static (unwrap)

cBasis :: Int -> C 2
cBasis i = fromList [ if j == i then 1 else 0 | j <- [0, 1] ]

main :: IO ()
main = do
  let xs = [fromList [1:+1, (-2):+2, (-1):+1] :: C 3, fromList [2:+(-2), (-1):+1, 2:+(-1)] :: C 3]
      ys = [fromList [(-1):+0, 2:+2] :: C 2, fromList [1:+(-1), (-2):+0] :: C 2]
      imgs = [ x ⊗ y | (x, y) <- zip xs ys ]
      m = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs)
        :: C 2 +> (C 3 ⊗ C 2)
      linMap = getLinearMap m
      manual j =
        unsafeFromArray @(C 3 ⊗ C 2)
          (HM.fromList (HM.toList (HM.toRows (extract linMap) !! j)))
      inlineApply v =
        sumV
          [ (unwrap v VS.! i)
              *^ unsafeFromArray @(C 3 ⊗ C 2)
                   (HM.fromList (HM.toList (HM.toRows (extract linMap) !! i)))
          | i <- [0, 1]
          ]
  putStrLn "expected 0:"
  print (VS.toList (toArray (imgs !! 0)))
  putStrLn "manual 0:"
  print (VS.toList (toArray (manual 0)))
  putStrLn "inline 0:"
  print (VS.toList (toArray (inlineApply (cBasis 0))))
  putStrLn "applyLinear 0:"
  print (VS.toList (toArray (getLinearFunction (applyLinear -+$> m) (cBasis 0))))
  putStrLn "arr 0:"
  print (VS.toList (toArray (arr m (cBasis 0))))
  putStrLn "m$ 0:"
  print (VS.toList (toArray (m $ cBasis 0)))
