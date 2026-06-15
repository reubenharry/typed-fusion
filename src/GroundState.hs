{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Dense ground-state solver for a local effective Hamiltonian.
--
-- This is the pragmatic, hmatrix-backed route to the local eigenproblem that
-- DMRG needs (see ROADMAP §4, decision D3): we materialise the operator as a
-- dense complex matrix and use hmatrix's Hermitian eigensolver. It is *not*
-- basis-independent and it builds the full matrix — fine for the local site
-- problem, and it lets us focus effort on defining the effective Hamiltonian
-- rather than on a Krylov solver. A matrix-free / basis-independent version can
-- replace this later (and move upstream into linearmap-family).
--
-- The solver is generic over the operand space @v@: any
-- @(FiniteDimensional v, InnerSpace v, Scalar v ~ Complex Double)@ works. In
-- particular @v@ may itself be a /linear-map space/ (e.g. the MPS centre
-- @(C b ⊗ C p) +> C b@), since linear maps form a first-class
-- 'FiniteDimensional' vector space in linearmap-category. So an effective
-- Hamiltonian @Heff :: (C b ⊗ C p +> C b) +> (C b ⊗ C p +> C b)@ — an
-- endomorphism on a map-space — is solved directly, no flattening to @C n@.
module GroundState
  ( toDenseMatrix
  , groundState
  , spectrum
  ) where

import Prelude hiding (($))
import Control.Arrow.Constrained (($))
import Math.LinearMap.Category
  ( type (+>), FiniteDimensional (..), SubBasis )
import Data.VectorSpace (InnerSpace (..), Scalar)
-- Orphan instances making @C n@ (and tensors/maps over it) linearmap-category
-- vector spaces / TensorSpaces (the instances that @$@-application and the
-- FiniteDimensional/HilbertSpace machinery need).
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import qualified Numeric.LinearAlgebra as H
import Data.Complex (Complex)

-- | The standard basis vectors of @v@ (linearmap-category's canonical finite
-- basis). For @C n@ and tensor/map spaces over it these have real 0/1 entries,
-- which is what makes the matrix read-off below convention-free.
basisOf :: forall v. FiniteDimensional v => [v]
basisOf = enumerateSubBasis (entireBasis :: SubBasis v)

-- | Materialise an endomorphism @v +> v@ as a dense complex matrix in the
-- canonical basis. Entry @(i, j)@ is the @i@-th coordinate of @f@ applied to
-- the @j@-th basis vector, read off as @e_i \<.\> (f e_j)@. Because the basis
-- vectors are real, this is the genuine operator matrix regardless of the
-- inner product's conjugation convention.
toDenseMatrix
  :: forall v. (FiniteDimensional v, InnerSpace v, Scalar v ~ Complex Double)
  => (v +> v) -> H.Matrix (Complex Double)
toDenseMatrix f =
  let es   = basisOf @v
      cols = [ f $ e | e <- es ]            -- f e_j, as vectors in v
  in H.fromLists [ [ ei <.> colj | colj <- cols ] | ei <- es ]

-- | Full (real) spectrum of a Hermitian operator, ascending.
spectrum
  :: forall v. (FiniteDimensional v, InnerSpace v, Scalar v ~ Complex Double)
  => (v +> v) -> [Double]
spectrum f =
  let (vals, _) = H.eigSH (H.sym (toDenseMatrix f))
  in reverse (H.toList vals)   -- eigSH returns descending; ascending is friendlier

-- | Lowest eigenpair of a Hermitian operator: @(eigenvalue, eigenvector)@.
--
-- The operator is symmetrised to its Hermitian part before solving, so a
-- not-quite-Hermitian @Heff@ (e.g. from rounding) is handled gracefully — at
-- the cost of masking a genuinely non-Hermitian bug, so callers should ensure
-- @Heff@ really is Hermitian.
groundState
  :: forall v. (FiniteDimensional v, InnerSpace v, Scalar v ~ Complex Double)
  => (v +> v) -> (Double, v)
groundState f =
  let (vals, vecs) = H.eigSH (H.sym (toDenseMatrix f))
      idx          = H.minIndex vals
      eval         = vals `H.atIndex` idx
  in case drop idx (H.toColumns vecs) of
       (evec : _) ->
         let coords     = H.toList evec
             (vec, _)   = recomposeSB (entireBasis :: SubBasis v) coords
         in (eval, vec)
       []         -> error "GroundState.groundState: empty eigenvector set"
