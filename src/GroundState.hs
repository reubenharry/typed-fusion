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
module GroundState
  ( toDenseMatrix
  , groundState
  , spectrum
  ) where

import Prelude hiding (($))
import Control.Arrow.Constrained (($))
import Math.LinearMap.Category (type (+>))
-- Orphan instances making @C n@ a linearmap-category vector space / TensorSpace
-- (the @Num'@/@LinearSpace@ instances that @$@-application needs).
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, create, extract)
import qualified Numeric.LinearAlgebra as H
import Data.Complex (Complex)
import GHC.TypeLits (KnownNat, natVal)
import Data.Proxy (Proxy (..))
import Data.Maybe (fromMaybe)

-- | The dimension of @C n@ as a value.
cdim :: forall n. KnownNat n => Int
cdim = fromIntegral (natVal (Proxy @n))

-- | @i@-th standard basis vector of @C n@.
basisVec :: forall n. KnownNat n => Int -> C n
basisVec i =
  fromMaybe (error "GroundState.basisVec: create failed") $
    create (H.fromList [ if j == i then 1 else 0 | j <- [0 .. cdim @n - 1] ])

-- | Materialise an endomorphism @C n +> C n@ as a dense complex matrix by
-- applying it to each standard basis vector. Column @i@ is @m@ applied to
-- @e_i@, so the matrix acts on the left in the usual convention
-- (@mat \<> v@). This makes the orientation unambiguous regardless of how the
-- 'LinearMap' stores its 'TensorProduct'.
toDenseMatrix :: forall n. KnownNat n => (C n +> C n) -> H.Matrix (Complex Double)
toDenseMatrix m =
  H.fromColumns [ extract (m $ basisVec @n i) | i <- [0 .. cdim @n - 1] ]

-- | Full (real) spectrum of a Hermitian operator, ascending.
spectrum :: forall n. KnownNat n => (C n +> C n) -> [Double]
spectrum m =
  let (vals, _) = H.eigSH (H.sym (toDenseMatrix m))
  in reverse (H.toList vals)   -- eigSH returns descending; ascending is friendlier

-- | Lowest eigenpair of a Hermitian operator: @(eigenvalue, eigenvector)@.
--
-- The operator is symmetrised to its Hermitian part before solving, so a
-- not-quite-Hermitian @Heff@ (e.g. from rounding) is handled gracefully — at
-- the cost of masking a genuinely non-Hermitian bug, so callers should ensure
-- @Heff@ really is Hermitian.
groundState :: forall n. KnownNat n => (C n +> C n) -> (Double, C n)
groundState m =
  let (vals, vecs) = H.eigSH (H.sym (toDenseMatrix m))
      idx          = H.minIndex vals
      eval         = vals `H.atIndex` idx
  in case drop idx (H.toColumns vecs) of
       (evec : _) -> (eval, fromMaybe (error "GroundState.groundState: create failed") (create evec))
       []         -> error "GroundState.groundState: empty eigenvector set"
