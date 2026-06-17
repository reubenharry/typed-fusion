{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Ground-state solver for a local effective Hamiltonian (ROADMAP §4b).
--
-- * 'groundState' / 'spectrum' use dense @hmatrix@ 'eigSH' on 'toDenseMatrix'
--   (interim default for map-space centres until map-space 'eigen' is unblocked).
-- * 'groundStateEigen' / 'spectrumEigen' use linearmap's matrix-free 'eigen' with
--   a supplied 'Norm' — works on 'HilbertSpace' types (@DualVector v ~ v@, e.g.
--   @'C' n@); map-space centres currently hit a Krylov slice bug in
--   @linearmap-hmatrix@.
--
-- 'hilbertSchmidtNorm' and 'toDenseMatrix' are exported for tests and the
-- eventual full map-space migration.
module GroundState
  ( toDenseMatrix
  , hilbertSchmidtNorm
  , groundStateDense
  , spectrumDense
  , groundStateEigen
  , spectrumEigen
  , groundState
  , spectrum
  ) where

import Prelude hiding (($))
import Control.Arrow.Constrained (($))
import Math.LinearMap.Category
  ( type (+>), FiniteDimensional (..), SubBasis
  , eigen, Norm (..), LSpace )
import Data.VectorSpace (InnerSpace (..), Scalar)
import Data.Number.NormedAlgebra (NormedAlgebra (RealPart))
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import qualified Numeric.LinearAlgebra as H
import Data.Complex (Complex, realPart)
import Data.List (sort, minimumBy)
import Data.Ord (comparing)
import Numeric.IEEE (IEEE)

-- | The standard basis vectors of @v@ (linearmap-category's canonical finite
-- basis). For @C n@ and tensor/map spaces over it these have real 0/1 entries,
-- which is what makes the matrix read-off below convention-free.
basisOf :: forall v. FiniteDimensional v => [v]
basisOf = enumerateSubBasis (entireBasis :: SubBasis v)

-- | Hilbert–Schmidt norm via 'uncanonicallyToDual' (for future map-space 'eigen').
hilbertSchmidtNorm :: FiniteDimensional v => Norm v
hilbertSchmidtNorm = Norm uncanonicallyToDual

-- | Materialise an endomorphism as a dense matrix in the canonical basis
-- (@e_i \<.\> f e_j@). Regression oracle and dense-solver input.
toDenseMatrix
  :: forall v. (FiniteDimensional v, InnerSpace v, Scalar v ~ Complex Double)
  => (v +> v) -> H.Matrix (Complex Double)
toDenseMatrix f =
  let es   = basisOf @v
      cols = [ f $ e | e <- es ]
  in H.fromLists [ [ ei <.> colj | colj <- cols ] | ei <- es ]

-- | Dense @hmatrix@ route (interim default).
groundStateDense
  :: forall v. (FiniteDimensional v, InnerSpace v, Scalar v ~ Complex Double)
  => (v +> v) -> (Double, v)
groundStateDense f =
  let (vals, vecs) = H.eigSH (H.sym (toDenseMatrix f))
      idx          = H.minIndex vals
      eval         = vals `H.atIndex` idx
  in case drop idx (H.toColumns vecs) of
       (evec : _) ->
         let coords   = H.toList evec
             (vec, _) = recomposeSB (entireBasis :: SubBasis v) coords
         in (eval, vec)
       [] -> error "GroundState.groundStateDense: empty eigenvector set"

spectrumDense
  :: ( FiniteDimensional v, InnerSpace v, Scalar v ~ Complex Double )
  => (v +> v) -> [Double]
spectrumDense f =
  let (vals, _) = H.eigSH (H.sym (toDenseMatrix f))
  in reverse (H.toList vals)

-- | Matrix-free 'eigen' route (Hilbert-space types today; map-space when unblocked).
groundStateEigen
  :: ( FiniteDimensional v, LSpace v, Scalar v ~ Complex Double
     , IEEE (RealPart (Scalar v)), RealFloat (RealPart (Scalar v))
     , Floating (Scalar v) )
  => Norm v -> (v +> v) -> (Double, v)
groundStateEigen norm f =
  case eigen norm f of
    [] -> error "GroundState.groundStateEigen: empty eigenvector set"
    pairs ->
      let (λ, vec) = minimumBy (comparing (realPart . fst)) pairs
      in (realPart λ, vec)

spectrumEigen
  :: ( FiniteDimensional v, LSpace v, Scalar v ~ Complex Double
     , IEEE (RealPart (Scalar v)), RealFloat (RealPart (Scalar v))
     , Floating (Scalar v) )
  => Norm v -> (v +> v) -> [Double]
spectrumEigen norm f =
  sort [ realPart λ | (λ, _) <- eigen norm f ]

-- | Lowest eigenpair of a Hermitian operator: @(eigenvalue, eigenvector)@.
groundState
  :: forall v. (FiniteDimensional v, InnerSpace v, Scalar v ~ Complex Double)
  => (v +> v) -> (Double, v)
groundState = groundStateDense

-- | Full (real) spectrum of a Hermitian operator, ascending.
spectrum
  :: ( FiniteDimensional v, InnerSpace v, Scalar v ~ Complex Double )
  => (v +> v) -> [Double]
spectrum = spectrumDense
