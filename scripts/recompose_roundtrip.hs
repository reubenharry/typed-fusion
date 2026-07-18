{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

-- | recomposeSB round-trip: basis_i ≈ recompose (e_i coords)
import Data.Complex (Complex, realPart)
import Data.VectorSpace (Scalar, InnerSpace ((<.>)), (^-^))
import Numeric.LinearAlgebra.Static (C)
import Math.LinearMap.Category
  ( type (+>), type (⊗)
  , FiniteDimensional (entireBasis, recomposeSB, enumerateSubBasis, subbasisDimension)
  , SubBasis
  )
import Numeric.LinearAlgebra.Static.COrphans ()
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()

nrm :: (InnerSpace v, Scalar v ~ Complex Double) => v -> Double
nrm v = sqrt (realPart (v <.> v))

checkRoundTrip
  :: forall v
   . (FiniteDimensional v, InnerSpace v, Scalar v ~ Complex Double)
  => String -> IO ()
checkRoundTrip label = do
  let bas = entireBasis :: SubBasis v
      es = enumerateSubBasis bas
      dim = subbasisDimension bas
      errs =
        [ nrm (e ^-^ fst (recomposeSB bas coords))
        | (i, e) <- zip [0 ..] es
        , let coords =
                [ if j == i then 1 else 0 | j <- [0 .. dim - 1] ]
        ]
      worst = maximum (0 : errs)
  putStrLn $
    label
      ++ "  dim="
      ++ show dim
      ++ "  max||e_i - recompose e_i||="
      ++ show worst
      ++ if worst < 1e-10 then "  OK" else "  FAIL"

main :: IO ()
main = do
  checkRoundTrip @(C 2) "C 2"
  checkRoundTrip @(C 2 ⊗ C 2) "C2 ⊗ C2"
  checkRoundTrip @(C 2 +> C 2) "C2 +> C2"
  checkRoundTrip @((C 2 ⊗ C 2) +> C 2) "(C2⊗C2) +> C2"
  checkRoundTrip @(C 2 +> (C 2 ⊗ C 2)) "C2 +> (C2⊗C2)"
