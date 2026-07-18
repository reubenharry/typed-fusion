{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Isolate recomposeSB failures by space.
import Control.Exception (evaluate, try, SomeException)
import Data.Complex (Complex)
import Data.VectorSpace (Scalar)
import Numeric.LinearAlgebra.Static (C)
import Math.LinearMap.Category
  ( type (+>), type (⊗)
  , FiniteDimensional (entireBasis, recomposeSB, subbasisDimension)
  , SubBasis
  )
import Numeric.LinearAlgebra.Static.COrphans ()
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()

tryRecompose
  :: forall v
   . (FiniteDimensional v, Scalar v ~ Complex Double)
  => String -> IO ()
tryRecompose label = do
  let n = subbasisDimension (entireBasis :: SubBasis v)
      coords = replicate n (1 :: Complex Double)
  outcome <- try (evaluate (fst (recomposeSB (entireBasis :: SubBasis v) coords) `seq` ()))
  case outcome of
    Left (ex :: SomeException) ->
      putStrLn $ "FAIL  " ++ label ++ "  dim=" ++ show n ++ "  " ++ show ex
    Right _ ->
      putStrLn $ "OK    " ++ label ++ "  dim=" ++ show n

main :: IO ()
main = do
  tryRecompose @(C 2) "C 2"
  tryRecompose @(C 2 ⊗ C 2) "C2 ⊗ C2"
  tryRecompose @(C 2 +> C 2) "C2 +> C2"
  tryRecompose @((C 2 ⊗ C 2) +> C 2) "(C2⊗C2) +> C2"
  tryRecompose @(C 2 +> (C 2 ⊗ C 2)) "C2 +> (C2⊗C2)"
