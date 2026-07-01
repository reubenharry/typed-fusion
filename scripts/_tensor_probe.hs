{-# LANGUAGE TypeApplications #-}
import Math.LinearMap.Category (TensorSpace (..), type (⊗))
import Math.LinearMap.Asserted (bilinearFunction, Bilinear)
import Numeric.LinearAlgebra.Static (C)
import Numeric.LinearAlgebra.Static.COrphans ()
import DirectSum (InfRep, InfRepTensor, emptyInfRep)
import Symmetry.Group (Group (..))

f :: Bilinear (C 2) (C 3) (C 2 ⊗ C 3)
f = tensorProduct @ (C 2)

main :: IO ()
main = print ()
