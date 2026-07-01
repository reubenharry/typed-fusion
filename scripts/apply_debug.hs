{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
import Prelude hiding (($))
import Control.Arrow.Constrained (($))
import Math.LinearMap.Category
  ( type (+>), type (⊗), (⊗), FiniteDimensional (..), SubBasis
  , recomposeLinMap, applyLinear, getLinearFunction, (-+$>), getLinearMap, LinearMap(..) )
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans (indexCnLinmap)
import Numeric.LinearAlgebra.Static (C, Sized (unwrap, extract))
import Data.Vector.Storable as VS
import Data.VectorSpace (sumV, (*^))
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import qualified Numeric.LinearAlgebra.HMatrix as HM
import qualified Numeric.LinearAlgebra as HMat
import TensorNetwork.MPS.Fixed3.Internal (basis)
import Data.Complex (Complex((:+)))

(=~=) :: Eq a => a -> a -> Bool
x =~= y = x == y

main :: IO ()
main = do
  let xs = [1 :+ 2, 0 :+ 1] :: [C 3]
      ys = [1 :+ 0, (-1) :+ 1] :: [C 2]
      imgs = [ x ⊗ y | (x, y) <- zip xs ys ]
      m = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs)
         :: C 2 +> (C 3 ⊗ C 2)
      LinearMap linMap = getLinearMap m
  putStrLn "=== decode paths ==="
  mapM_ (\j -> do
    let hmRow = HM.toList (HM.toRows (extract linMap) !! j)
        hmatRow = HMat.toList (HMat.toRows (extract linMap) !! j)
        manualHM = unsafeFromArray @(C 3 ⊗ C 2) (HM.fromList hmRow)
        manualHMat = unsafeFromArray @(C 3 ⊗ C 2) (HMat.fromList hmatRow)
        viaIndex = indexCnLinmap @2 @(C 3 ⊗ C 2) m j
        viaApply = getLinearFunction (applyLinear -+$> m) (basis @2 j)
        inline =
          sumV [ (unwrap (basis @2 j) VS.! i) *^ manualHM | i <- [0,1] ]
    putStrLn $ "\nj=" ++ show j ++ " target=" ++ show (VS.toList (toArray (imgs !! j)))
    putStrLn $ "  hmRow==hmatRow: " ++ show (hmRow == hmatRow)
    putStrLn $ "  manualHM==img: " ++ show (manualHM =~= imgs !! j)
    putStrLn $ "  manualHMat==img: " ++ show (manualHMat =~= imgs !! j)
    putStrLn $ "  indexCn==img: " ++ show (viaIndex =~= imgs !! j)
    putStrLn $ "  apply==img: " ++ show (viaApply =~= imgs !! j)
    putStrLn $ "  inline==img: " ++ show (inline =~= imgs !! j)
    putStrLn $ "  index==manualHM: " ++ show (viaIndex =~= manualHM)
    putStrLn $ "  apply==inline: " ++ show (viaApply =~= inline)
    ) [0, 1]
