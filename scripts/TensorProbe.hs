{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module TensorProbe where

import GHC.TypeLits (KnownNat)

import Math.LinearMap.Category (TensorSpace (tensorProduct), type (⊗))
import Math.LinearMap.Category.Class (contractBilinearFn)
import Math.LinearMap.Asserted (Bilinear)
import Numeric.LinearAlgebra.Static (C)
import Numeric.LinearAlgebra.Static.COrphans ()

probe :: C 2 -> C 3 -> C 2 ⊗ C 3
probe v w = contractBilinearFn (tensorProduct @(C 2) @(C 3)) v w
