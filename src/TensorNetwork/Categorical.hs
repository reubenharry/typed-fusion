{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoStarIsType #-}

-- | Morphism-level building blocks missing from @linearmap-category@'s export
-- surface, assembled from 'TensorSpace' \/ 'LinearSpace' primitives only — no
-- coefficient extraction, no @hmatrix@ index arithmetic.
--
-- These are the operations a tensor network actually wires diagrams with:
--
--   * '⊗^' — the monoidal product of morphisms,
--     @f ⊗^ g : (u ⊗ u') +> (v ⊗ v')@;
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
    -- * Boundary unitors ('BoundaryUnit', typically @Scalar bond@)
  , BoundaryUnit (..)
  , lunitAt
  , lunitInvAt
  , lunitScalarLeg
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
import qualified Prelude as Hask
import Control.Category.Constrained (id, (.))
import Control.Arrow.Constrained (arr, ($))
import Math.LinearMap.Category
  ( type (+>), type (⊗), Tensor (..), (⊗)
  , TensorSpace (..), TensorProduct, LinearSpace (..), LSpace
  , FiniteDimensional (..), Num' (..)
  , getAntilinearFunction, LinearMap (..)
  , LinearFunction, pattern LinearFunction, (-+$>), Dimensional
  , tensorOfMaps, applyDualVector, HilbertSpace, DualVector )
import Math.LinearMap.Coercion (lassocTensor, rassocTensor, (-+$=>))
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.VectorSpace.DimensionAware
  ( toArray, unsafeFromArray, Dimension, dimensionalitySing
  , dimensionality, DimensionalityCases (StaticDimensionalCase) )
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, Sized (konst), M, extract)
import qualified Numeric.LinearAlgebra.HMatrix as HM
import GHC.TypeLits (KnownNat, type (*), natVal)
import Data.Proxy (Proxy (..))
import qualified Data.Vector.Storable as VS
import Data.Complex (Complex ((:+)))
import Unsafe.Coerce (unsafeCoerce)
import Data.VectorSpace (Scalar, VectorSpace ((*^)))
import Math.OrphanInstances ()

-- | Scalar field shorthand for this module.
type ℂ = Complex Double

-- | Monoidal product of linear maps via basis recomposition:
--
--   @(f ⊗^ g) $ (x ⊗ y) = (f $ x) ⊗ (g $ y)@
(⊗^)
  :: forall u v u' v'
   . ( LSpace u, LSpace u', LSpace v, LSpace v'
     , FiniteDimensional u, FiniteDimensional u'
     , TensorSpace v, TensorSpace v'
     , TensorSpace (u ⊗ u'), TensorSpace (v ⊗ v')
     , Num' (Scalar v), Fractional (Scalar v), Eq (Scalar v)
     , Scalar u ~ ℂ, Scalar u' ~ ℂ, Scalar v ~ ℂ, Scalar v' ~ ℂ
     , Scalar u ~ Scalar u', Scalar u ~ Scalar v, Scalar v ~ Scalar v'
     , Scalar (DualVector u) ~ ℂ, Scalar (DualVector u') ~ ℂ
     , Scalar (DualVector u) ~ Scalar v'
     , Scalar (DualVector u') ~ Scalar v )
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
-- TODO: presumably there should be a general map from a 1D space to the scalar field: i assume this is in linearmap-family somewhere
scalarizeC1 :: LinearFunction ℂ (C 1) ℂ
scalarizeC1 = applyDualVector -+$> oneC1

-- | Embed a scalar as a @C 1@ leg: @ℂ -+> C 1@.
unscalarizeC1 :: LinearFunction ℂ ℂ (C 1)
unscalarizeC1 = LinearFunction (*^ oneC1)

-- | A one-dimensional Hilbert space used as the monoidal unit at open MPS
-- boundaries. For static MPS this is typically @Scalar bond ~ ℂ@; @C 1@ is also
-- supported for typed bond legs.
class
  ( TensorSpace unit, LinearSpace unit
  , HilbertSpace unit
  , DualVector unit ~ unit, Scalar unit ~ ℂ
  ) =>
  BoundaryUnit unit
  where
    unitVector :: unit
    scalarizeUnit :: LinearFunction ℂ unit ℂ
    unscalarizeUnit :: LinearFunction ℂ ℂ unit

instance BoundaryUnit (C 1) where
  unitVector = oneC1
  scalarizeUnit = scalarizeC1
  unscalarizeUnit = unscalarizeC1

instance BoundaryUnit (Complex Double) where
  unitVector = 1 :+ 0
  scalarizeUnit = LinearFunction Hask.id
  unscalarizeUnit = LinearFunction Hask.id

-- | Left unitor when the boundary is the scalar field @s@ and
-- @TensorProduct s v ~ v@ (so @s ⊗ v@ is stored as @Tensor v@).
lunitScalarLeg
  :: forall v
   . ( BoundaryUnit (Complex Double), Num' (Complex Double)
     , LinearSpace v, TensorSpace v, TensorSpace (Complex Double ⊗ v)
     , Scalar v ~ Complex Double
     , TensorProduct (Complex Double) v ~ v )
  => (Complex Double ⊗ v) +> v
lunitScalarLeg = arr (LinearFunction getTensorProduct)

-- | Left unitor at an abstract boundary unit: @(unit ⊗ v) +> v@.
lunitAt
  :: forall unit v
   . ( BoundaryUnit unit
     , LinearSpace v, TensorSpace v, TensorSpace (unit ⊗ v)
     , Scalar v ~ ℂ )
  => (unit ⊗ v) +> v
lunitAt = arr (fromFlatTensor . (fmapTensor -+$> scalarizeUnit @unit) . transposeTensor)

-- | Inverse left unitor: @v +> (unit ⊗ v)@.
lunitInvAt
  :: forall unit v
   . ( BoundaryUnit unit
     , LinearSpace v, TensorSpace v, TensorSpace (unit ⊗ v)
     , Scalar v ~ ℂ )
  => v +> (unit ⊗ v)
lunitInvAt =
  arr (transposeTensor . (fmapTensor -+$> unscalarizeUnit @unit) . toFlatTensor)

-- | Left unitor at the @C 1@ boundary bond: @(C 1 ⊗ v) +> v@.
lunit
  :: forall v. (LinearSpace v, Scalar v ~ ℂ, TensorSpace (C 1 ⊗ v))
  => (C 1 ⊗ v) +> v
lunit = lunitAt @(C 1) @v

-- | Inverse left unitor: @v +> (C 1 ⊗ v)@.
lunitInv
  :: forall v. (LinearSpace v, Scalar v ~ ℂ, TensorSpace (C 1 ⊗ v))
  => v +> (C 1 ⊗ v)
lunitInv = lunitInvAt @(C 1) @v

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

-- -- | Inverse of 'fuseBond': @C (a·b) +> (C a ⊗ C b)@.
-- splitBond
--   :: forall a b. (KnownNat a, KnownNat b, KnownNat (a * b))
--   => C (a * b) +> (C a ⊗ C b)
-- splitBond = arr (LinearFunction (unsafeFromArray . asArray))
--   where
--     asArray :: C (a * b) -> VS.Vector ℂ
--     asArray = toArray


-- | Inverse of 'fuseBond': @C (a·b) +> (C a ⊗ C b)@.
splitBond
  :: forall a b v1 v2 w. (LinearSpace v1, LinearSpace v2, LinearSpace w, KnownNat a, KnownNat b, KnownNat (a * b), (a*b) `Dimensional` w, a `Dimensional` v1, b `Dimensional` v2, Scalar v1 ~ ℂ, Scalar v2 ~ ℂ, Scalar w ~ ℂ)
  => w +> (v1 ⊗ v2)
splitBond = arr (LinearFunction (unsafeFromArray . asArray))
  where
    asArray :: w -> VS.Vector ℂ
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
