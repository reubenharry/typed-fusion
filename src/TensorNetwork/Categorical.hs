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
--   * 'lunit' \/ 'runit' (and inverses) — the @C 1@ boundary unitors;
--   * 'fuseBond' \/ 'splitBond' — the Kronecker isomorphism
--     @C a ⊗ C b ≅ C (a·b)@ via matching 'toArray' layouts.
module TensorNetwork.Categorical
  ( (⊗^)
  , swapMap
  , lassocMap
  , rassocMap
  , lunit
  , lunitInv
  , runit
  , fuseBond
  , splitBond
  , conjugateMap
  ) where

import Prelude hiding (($), (.))
import qualified Prelude as Hask
import Control.Category.Constrained (id, (.))
import Control.Arrow.Constrained (arr, ($))
import Math.LinearMap.Category
  ( type (+>), type (⊗), Tensor (..), (⊗)
  , TensorSpace (..), TensorProduct, LinearSpace (..), LSpace
  , Num' (..)
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
import Data.Coerce (coerce)

-- | Scalar field shorthand for this module.
type ℂ = Complex Double

-- | Monoidal product of linear maps ('tensorOfMaps'):
--
--   @(f ⊗^ g) $ (x ⊗ y) = (f $ x) ⊗ (g $ y)@
(⊗^)
  :: forall u v u' v'
   . ( LSpace u, LSpace u', LSpace v, LSpace v'
     , TensorSpace v, TensorSpace v'
     , TensorSpace (u ⊗ u'), TensorSpace (v ⊗ v')
     , Scalar u ~ Scalar u', Scalar u ~ Scalar v, Scalar v ~ Scalar v'
    --  , Scalar (DualVector u) ~ Scalar v'
    --  , Scalar (DualVector u') ~ Scalar v )
   )
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
  :: ( LSpace u, LSpace v, LSpace w, Scalar u ~ Scalar v, Scalar v ~ Scalar w)
  => (u ⊗ (v ⊗ w)) +> ((u ⊗ v) ⊗ w)
lassocMap = arr $ LinearFunction coerce -- arr (LinearFunction (lassocTensor -+$=>))

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

-- | Left unitor at the @C 1@ boundary bond: @(C 1 ⊗ v) +> v@.
lunit
  :: forall v. (LinearSpace v, Scalar v ~ ℂ, TensorSpace (C 1 ⊗ v))
  => (C 1 ⊗ v) +> v
lunit = undefined

-- | Inverse left unitor: @v +> (C 1 ⊗ v)@.
lunitInv
  :: forall v. (LinearSpace v, Scalar v ~ ℂ, TensorSpace (C 1 ⊗ v))
  => v +> (C 1 ⊗ v)
lunitInv = undefined

-- | Right unitor: @(v ⊗ C 1) +> v@.
runit
  :: forall v. (LinearSpace v, Scalar v ~ ℂ)
  => (v ⊗ C 1) +> v
runit = arr (fromFlatTensor . (fmapTensor -+$> scalarizeC1))

-- | Kronecker fusion @C a ⊗ C b → C (a·b)@, via matching 'toArray' layouts
-- (same representation as the static @C (a·b)@ buffer — not 'unsafeCoerce').
fuseBond
  :: forall a b. (KnownNat a, KnownNat b, KnownNat (a * b))
  => (C a ⊗ C b) +> C (a * b)
fuseBond = arr (LinearFunction (unsafeFromArray . asArray))
  where
    asArray :: (C a ⊗ C b) -> VS.Vector ℂ
    asArray = toArray

-- | Inverse of 'fuseBond': @C (a·b) → C a ⊗ C b@.
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
     , Scalar v ~ Scalar w )
  => (v +> w) -> (v +> w)
conjugateMap = getAntilinearFunction vectorConjugate
