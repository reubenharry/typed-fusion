{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE NoStarIsType #-}

-- | Morphism-level building blocks missing from @linearmap-category@'s export
-- surface, assembled from 'TensorSpace' \/ 'LinearSpace' primitives only — no
-- coefficient extraction, no @hmatrix@ index arithmetic.
--
-- These are the operations a tensor network actually wires diagrams with:
--
--   * '⊗^' — the monoidal product of morphisms,
--     @f ⊗^ g : (u ⊗ u') +> (v ⊗ v')@ (fork's 'tensorOfMaps');
--   * 'swapMap', 'lassocMap', 'rassocMap' — braiding and associators as
--     first-class @+>@ morphisms;
--   * 'lunit' \/ 'runit' (and inverses) — the @C 1@ boundary unitors.
module TensorNetwork.Categorical
  ( -- * Monoidal product of maps
    (⊗^)
    -- * Wiring: braiding and associators
  , swapMap
  , lassocMap
  , rassocMap
    -- * Boundary (C 1) unitors
  , lunit
  , lunitInv
  , runit
  , runitInv
    -- * Bond fusion
  , fuseBond
  , splitBond
    -- * Conjugation
  , conjugateMap
  ) where

import Prelude hiding (($), (.))
import Control.Category.Constrained (id, (.))
import Control.Arrow.Constrained (arr, ($))
import Math.LinearMap.Category
  ( type (+>), type (⊗), Tensor
  , TensorSpace (..), LinearSpace (..)
  , tensorOfMaps, getAntilinearFunction
  , LinearFunction, pattern LinearFunction, (-+$>) )
import Math.LinearMap.Coercion (lassocTensor, rassocTensor, (-+$=>))
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, Sized (konst))
import GHC.TypeLits (KnownNat, type (*))
import qualified Data.Vector.Storable as VS
import Data.Complex (Complex)
import Data.VectorSpace (Scalar, VectorSpace ((*^)))

-- | Scalar field shorthand for this module.
type ℂ = Complex Double

-- | Monoidal (Kronecker) product of linear maps:
--
--   @(f ⊗^ g) $ (x ⊗ y) = (f $ x) ⊗ (g $ y)@
--
-- Plain-function form of the fork's 'tensorOfMaps'.
(⊗^)
  :: ( LinearSpace u, LinearSpace u', TensorSpace v, TensorSpace v'
     , Scalar u ~ ℂ, Scalar u' ~ ℂ, Scalar v ~ ℂ, Scalar v' ~ ℂ )
  => (u +> v) -> (u' +> v') -> ((u ⊗ u') +> (v ⊗ v'))
f ⊗^ g = (tensorOfMaps -+$> f) -+$> g
infixr 7 ⊗^

-- | The braiding @σ : (u ⊗ v) +> (v ⊗ u)@ ('transposeTensor' as a morphism).
swapMap
  :: ( LinearSpace u, LinearSpace v
     , Scalar u ~ ℂ, Scalar v ~ ℂ )
  => (u ⊗ v) +> (v ⊗ u)
swapMap = arr transposeTensor

-- | The associator @α : (u ⊗ (v ⊗ w)) +> ((u ⊗ v) ⊗ w)@ ('lassocTensor' as a
-- morphism).
lassocMap
  :: ( LinearSpace u, LinearSpace v, LinearSpace w
     , Scalar u ~ ℂ, Scalar v ~ ℂ, Scalar w ~ ℂ )
  => (u ⊗ (v ⊗ w)) +> ((u ⊗ v) ⊗ w)
lassocMap = arr (LinearFunction (lassocTensor -+$=>))

-- | Inverse associator @α⁻¹ : ((u ⊗ v) ⊗ w) +> (u ⊗ (v ⊗ w))@.
rassocMap
  :: ( LinearSpace u, LinearSpace v, LinearSpace w
     , Scalar u ~ ℂ, Scalar v ~ ℂ, Scalar w ~ ℂ )
  => ((u ⊗ v) ⊗ w) +> (u ⊗ (v ⊗ w))
rassocMap = arr (LinearFunction (rassocTensor -+$=>))

-- | @1 ∈ C 1@, the canonical basis vector of the boundary bond.
oneC1 :: C 1
oneC1 = konst 1

-- | Pair a @C 1@ leg against @1@, leaving the scalar: @C 1 -+> ℂ@.
scalarizeC1 :: LinearFunction ℂ (C 1) ℂ
scalarizeC1 = applyDualVector -+$> oneC1

-- | Embed a scalar as a @C 1@ leg: @ℂ -+> C 1@.
unscalarizeC1 :: LinearFunction ℂ ℂ (C 1)
unscalarizeC1 = LinearFunction (*^ oneC1)

-- | Left unitor at the @C 1@ boundary bond: @(C 1 ⊗ v) +> v@.
lunit
  :: forall v. (LinearSpace v, Scalar v ~ ℂ)
  => (C 1 ⊗ v) +> v
lunit = arr (fromFlatTensor . (fmapTensor -+$> scalarizeC1) . transposeTensor)

-- | Inverse left unitor: @v +> (C 1 ⊗ v)@.
lunitInv
  :: forall v. (LinearSpace v, Scalar v ~ ℂ)
  => v +> (C 1 ⊗ v)
lunitInv = arr (transposeTensor . (fmapTensor -+$> unscalarizeC1) . toFlatTensor)

-- | Right unitor: @(v ⊗ C 1) +> v@.
runit
  :: forall v. (LinearSpace v, Scalar v ~ ℂ)
  => (v ⊗ C 1) +> v
runit = arr (fromFlatTensor . (fmapTensor -+$> scalarizeC1))

-- | Inverse right unitor: @v +> (v ⊗ C 1)@.
runitInv
  :: forall v. (LinearSpace v, Scalar v ~ ℂ)
  => v +> (v ⊗ C 1)
runitInv = arr ((fmapTensor -+$> unscalarizeC1) . toFlatTensor)

-- | Fuse a tensor of bonds into a single typed bond, @(C a ⊗ C b) +> C (a·b)@.
--
-- This is the (strictifying) isomorphism between the typed tensor and its
-- flat bond space, realised through the backend's canonical array order
-- (co-lexicographic: fused index @j·a + i@ for @e_i ⊗ e_j@). It is the one
-- place where a basis order is chosen — by 'Dimensional', not by ad-hoc
-- matrix reshaping — and 'splitBond' is its exact inverse.
fuseBond
  :: forall a b. (KnownNat a, KnownNat b, KnownNat (a * b))
  => (C a ⊗ C b) +> C (a * b)
fuseBond = arr (LinearFunction (unsafeFromArray . asArray))
  where
    asArray :: (C a ⊗ C b) -> VS.Vector ℂ
    asArray = toArray

-- | Inverse of 'fuseBond': @C (a·b) +> (C a ⊗ C b)@.
splitBond
  :: forall a b. (KnownNat a, KnownNat b, KnownNat (a * b))
  => C (a * b) +> (C a ⊗ C b)
splitBond = arr (LinearFunction (unsafeFromArray . asArray))
  where
    asArray :: C (a * b) -> VS.Vector ℂ
    asArray = toArray

-- | Entry-wise complex conjugation of a linear map, via 'vectorConjugate' on
-- the map's own 'TensorSpace' structure (a @+>@ map is itself a vector).
-- Antilinear; the single conjugation point for bra formation
-- (memory @conjugation-conventions@).
conjugateMap
  :: ( LinearSpace v, TensorSpace w
     , Scalar v ~ ℂ, Scalar w ~ ℂ )
  => (v +> w) -> (v +> w)
conjugateMap = getAntilinearFunction vectorConjugate
