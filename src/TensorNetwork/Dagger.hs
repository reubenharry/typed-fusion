{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Hilbert-space adjoint (†) for finite-dimensional complex spaces.
--
-- @dagger f@ is the conjugate transpose: 'conjugateMap' (entry-wise
-- 'vectorConjugate' on the map's own vector-space structure) composed with the
-- categorical 'adjoint' (transpose) and the dual→primal identification
-- 'hilbertFromDual'. Note † is /antilinear/, so it is exposed as a plain
-- function, not a @-+>@ morphism.
module TensorNetwork.Dagger
  ( dagger
  , transposeMap
  , hilbertFromDual
  ) where

import Prelude hiding (($))
import qualified Control.Category.Constrained as Cat
import qualified Control.Functor.Constrained as CF
import Math.LinearMap.Category
  ( type (-+>), type (+>), type (⊗), adjoint, (-+$>)
  , Scalar, TensorSpace, LinearSpace, DualVector
  , DualSpaceWitness (..), dualSpaceWitness
  , FiniteDimensional, uncanonicallyFromDual )
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C)
import GHC.TypeLits (KnownNat)
import Data.Complex (Complex)
import TensorNetwork.Categorical (conjugateMap)

-- | Identify a dual vector with its primal Hilbert representative.
--
-- This is the locus for the dual→primal choice (ROADMAP §4a step 5): for
-- tensor spaces it discharges @DualVector (u ⊗ v) ≅ u ⊗ v@ through
-- @LinearMap u (DualVector v)@. On the static @C n@ backend it is @id@
-- (inner-product-compatible).
hilbertFromDual
  :: forall v. (TensorSpace v, FiniteDimensional v) => DualVector v -+> v
hilbertFromDual = uncanonicallyFromDual

-- | Plain (unconjugated) transpose of @f : v +> w@, for a self-dual codomain
-- (@DualVector w ~ w@, e.g. @C n@): the categorical 'adjoint' followed by the
-- dual→primal identification. Linear (unlike 'dagger').
transposeMap
  :: forall v w.
     ( LinearSpace v, FiniteDimensional v
     , LinearSpace w, DualVector w ~ w
     , Scalar v ~ Complex Double, Scalar w ~ Complex Double )
  => (v +> w) -> (w +> v)
transposeMap f = case dualSpaceWitness @v of
  DualSpaceWitness ->
    (CF.fmap (hilbertFromDual @v) Cat.. adjoint @v @w) -+$> f

-- | Conjugate transpose @f†@ of @f : v +> w@, for a self-dual codomain
-- (@DualVector w ~ w@, e.g. @C n@): conjugate entries, then 'transposeMap'.
dagger
  :: forall v w.
     ( LinearSpace v, FiniteDimensional v
     , LinearSpace w, DualVector w ~ w
     , Scalar v ~ Complex Double, Scalar w ~ Complex Double )
  => (v +> w) -> (w +> v)
dagger f = transposeMap (conjugateMap f)

-- | MPS site †: @((C bl ⊗ C p) +> C br) → (C br +> (C bl ⊗ C p))@.
-- Monomorphic alias of 'dagger' at the site shape.
-- siteDagger
--   :: forall bl p br. (KnownNat bl, KnownNat p, KnownNat br)
--   => ((C bl ⊗ C p) +> C br) -> (C br +> (C bl ⊗ C p))
-- siteDagger = dagger
