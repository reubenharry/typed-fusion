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
--     @C a ⊗ C b ≅ C (a·b)@ via matching 'toArray' layouts;
--   * 'mergeCopyAxis' \/ 'flattenCopyProd' \/ 'flattenTensorProdCopy' —
--     copy-axis direct sum and @'Prod'@→@'AtomM'@ flattening at the same
--     canonical array boundary.
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
  , mergeCopyAxis
  , mergeCopyAxisTensor
  , mergeCopyAxisTensorLeft
  , tensorProdLeft
  , flattenCopyProd
  , flattenTensorProdCopy
  , conjugateMap
  ) where

import Prelude hiding (($), (.))
import qualified Prelude as Hask
import Control.Category.Constrained (id, (.))
import qualified Control.Category.Constrained as Cat
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
import GHC.TypeLits (KnownNat, type (*), type (+), natVal)
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

-- | Direct sum along the copy factor: @C m₁ ⊗ C d@ and @C m₂ ⊗ C d@ stack into
-- @C (m₁+m₂) ⊗ C d@ (same Kronecker layout as 'fuseBond').
mergeCopyAxis
  :: forall m1 m2 d
   . ( KnownNat m1
     , KnownNat m2
     , KnownNat d
     , KnownNat (m1 + m2)
     , LSpace (C d)
     , LSpace (C m1)
     , LSpace (C m2)
     , LSpace (C (m1 + m2))
     , LSpace (C m1 ⊗ C d)
     , LSpace (C m2 ⊗ C d)
     , LSpace (C (m1 + m2) ⊗ C d)
     , TensorSpace (C m1 ⊗ C d)
     , TensorSpace (C m2 ⊗ C d)
     , TensorSpace (C (m1 + m2) ⊗ C d)
     , Scalar (C d) ~ ℂ
     , Scalar (C m1) ~ ℂ
     , Scalar (C m2) ~ ℂ
     , Scalar (C m1 ⊗ C d) ~ ℂ
     , Scalar (C m2 ⊗ C d) ~ ℂ
     , Scalar (C (m1 + m2) ⊗ C d) ~ ℂ
     )
  => (C m1 ⊗ C d) -> (C m2 ⊗ C d) -> (C (m1 + m2) ⊗ C d)
mergeCopyAxis v1 v2 =
  unsafeFromArray @(C (m1 + m2) ⊗ C d) $
    VS.concat [toArray v1, toArray v2]

-- | Like 'mergeCopyAxis', with irrep tail @C j₁ ⊗ C j₂@ (tensor sectors).
mergeCopyAxisTensor
  :: forall m1 m2 j1 j2
   . ( KnownNat m1
     , KnownNat m2
     , KnownNat j1
     , KnownNat j2
     , KnownNat (m1 + m2)
     , LSpace (C j1)
     , LSpace (C j2)
     , LSpace (C j1 ⊗ C j2)
     , LSpace (C m1)
     , LSpace (C m2)
     , LSpace (C (m1 + m2))
     , LSpace (C m1 ⊗ (C j1 ⊗ C j2))
     , LSpace (C m2 ⊗ (C j1 ⊗ C j2))
     , LSpace (C (m1 + m2) ⊗ (C j1 ⊗ C j2))
     , TensorSpace (C j1 ⊗ C j2)
     , TensorSpace (C m1 ⊗ (C j1 ⊗ C j2))
     , TensorSpace (C m2 ⊗ (C j1 ⊗ C j2))
     , TensorSpace (C (m1 + m2) ⊗ (C j1 ⊗ C j2))
     , Scalar (C j1) ~ ℂ
     , Scalar (C j2) ~ ℂ
     , Scalar (C m1) ~ ℂ
     , Scalar (C m2) ~ ℂ
     , Scalar (C m1 ⊗ (C j1 ⊗ C j2)) ~ ℂ
     , Scalar (C m2 ⊗ (C j1 ⊗ C j2)) ~ ℂ
     , Scalar (C (m1 + m2) ⊗ (C j1 ⊗ C j2)) ~ ℂ
     )
  => (C m1 ⊗ (C j1 ⊗ C j2))
  -> (C m2 ⊗ (C j1 ⊗ C j2))
  -> (C (m1 + m2) ⊗ (C j1 ⊗ C j2))
mergeCopyAxisTensor v1 v2 =
  unsafeFromArray @(C (m1 + m2) ⊗ (C j1 ⊗ C j2)) $
    VS.concat [toArray v1, toArray v2]

-- | Like 'mergeCopyAxisTensor', for left-associated @((C m₁ ⊗ C j₁) ⊗ C j₂)@.
mergeCopyAxisTensorLeft
  :: forall m1 m2 j1 j2
   . ( KnownNat m1
     , KnownNat m2
     , KnownNat j1
     , KnownNat j2
     , KnownNat (m1 + m2)
     , LSpace (C j1)
     , LSpace (C j2)
     , LSpace (C m1)
     , LSpace (C m2)
     , LSpace (C (m1 + m2))
     , LSpace (C m1 ⊗ C j1)
     , LSpace (C m2 ⊗ C j1)
     , LSpace (C m1 ⊗ C j1 ⊗ C j2)
     , LSpace (C m2 ⊗ C j1 ⊗ C j2)
     , LSpace (C (m1 + m2) ⊗ C j1 ⊗ C j2)
     , LSpace ((C m1 ⊗ C j1) ⊗ C j2)
     , LSpace ((C m2 ⊗ C j1) ⊗ C j2)
     , LSpace ((C (m1 + m2) ⊗ C j1) ⊗ C j2)
     , TensorSpace ((C m1 ⊗ C j1) ⊗ C j2)
     , TensorSpace ((C m2 ⊗ C j1) ⊗ C j2)
     , TensorSpace ((C (m1 + m2) ⊗ C j1) ⊗ C j2)
     , Scalar (C j1) ~ ℂ
     , Scalar (C j2) ~ ℂ
     , Scalar (C m1) ~ ℂ
     , Scalar (C m2) ~ ℂ
     , Scalar ((C m1 ⊗ C j1) ⊗ C j2) ~ ℂ
     , Scalar ((C m2 ⊗ C j1) ⊗ C j2) ~ ℂ
     , Scalar ((C (m1 + m2) ⊗ C j1) ⊗ C j2) ~ ℂ
     )
  => ((C m1 ⊗ C j1) ⊗ C j2)
  -> ((C m2 ⊗ C j1) ⊗ C j2)
  -> ((C (m1 + m2) ⊗ C j1) ⊗ C j2)
mergeCopyAxisTensorLeft v1 v2 =
  unsafeFromArray @((C (m1 + m2) ⊗ C j1) ⊗ C j2) $
    VS.concat [toArray v1, toArray v2]

-- | Repackage @C m ⊗ (C j₁ ⊗ C j₂)@ to @((C m ⊗ C j₁) ⊗ C j₂)@ (same flat buffer).
tensorProdLeft
  :: forall m j1 j2
   . ( KnownNat m
     , KnownNat j1
     , KnownNat j2
     , LSpace (C j1)
     , LSpace (C j2)
     , LSpace (C m)
     , LSpace (C j1 ⊗ C j2)
     , LSpace (C m ⊗ (C j1 ⊗ C j2))
     , LSpace (C m ⊗ C j1)
     , LSpace ((C m ⊗ C j1) ⊗ C j2)
     , TensorSpace (C m ⊗ (C j1 ⊗ C j2))
     , TensorSpace ((C m ⊗ C j1) ⊗ C j2)
     , Scalar (C j1) ~ ℂ
     , Scalar (C j2) ~ ℂ
     , Scalar (C m) ~ ℂ
     , Scalar (C m ⊗ (C j1 ⊗ C j2)) ~ ℂ
     , Scalar ((C m ⊗ C j1) ⊗ C j2) ~ ℂ
     )
  => (C m ⊗ (C j1 ⊗ C j2))
  -> ((C m ⊗ C j1) ⊗ C j2)
tensorProdLeft v =
  unsafeFromArray @((C m ⊗ C j1) ⊗ C j2) (toArray v :: VS.Vector ℂ)

-- | Collapse factored copy legs @C m ⊗ C n@ into @C (m·n)@, holding @C d@ fixed
-- (@'fuseBond' ⊗^ id@).
flattenCopyProd
  :: forall m n d
   . ( KnownNat m
     , KnownNat n
     , KnownNat d
     , KnownNat (m * n)
     , LSpace (C d)
     , LSpace (C m)
     , LSpace (C n)
     , LSpace (C (m * n))
     , LSpace (C m ⊗ C n)
     , LSpace (C m ⊗ C d)
     , LSpace (C n ⊗ C d)
     , LSpace ((C m ⊗ C n) ⊗ C d)
     , LSpace (C (m * n) ⊗ C d)
     , TensorSpace (C m ⊗ C n)
     , TensorSpace (C (m * n))
     , TensorSpace ((C m ⊗ C n) ⊗ C d)
     , TensorSpace (C (m * n) ⊗ C d)
     , Scalar (C d) ~ ℂ
     , Scalar (C m) ~ ℂ
     , Scalar (C n) ~ ℂ
     , Scalar ((C m ⊗ C n) ⊗ C d) ~ ℂ
     , Scalar (C (m * n) ⊗ C d) ~ ℂ
     )
  => ((C m ⊗ C n) ⊗ C d) -> (C (m * n) ⊗ C d)
flattenCopyProd v = (fuseBond @m @n ⊗^ Cat.id) $ v

-- | Flatten @'Prod'@ copy layout on a tensor sector to @'AtomM'@ shape before
-- copy-axis merge. Same total dimension; array layout matches @ToVSectorE@ /
-- @Symmetry.CG.SU2@ Kronecker order.
flattenTensorProdCopy
  :: forall m n j1 j2
   . ( KnownNat m
     , KnownNat n
     , KnownNat (m * n)
     , KnownNat j1
     , KnownNat j2
     , LSpace (C j1)
     , LSpace (C j2)
     , LSpace (C m)
     , LSpace (C n)
     , LSpace (C m ⊗ C j1)
     , LSpace (C n ⊗ C j2)
     , LSpace (C j1 ⊗ C j2)
     , LSpace (C (m * n))
     , LSpace ((C m ⊗ C j1) ⊗ (C n ⊗ C j2))
     , LSpace (C (m * n) ⊗ (C j1 ⊗ C j2))
     , TensorSpace ((C m ⊗ C j1) ⊗ (C n ⊗ C j2))
     , TensorSpace (C (m * n) ⊗ (C j1 ⊗ C j2))
     , Scalar (C j1) ~ ℂ
     , Scalar (C j2) ~ ℂ
     , Scalar (C m) ~ ℂ
     , Scalar (C n) ~ ℂ
     , Scalar ((C m ⊗ C j1) ⊗ (C n ⊗ C j2)) ~ ℂ
     , Scalar (C (m * n) ⊗ (C j1 ⊗ C j2)) ~ ℂ
     )
  => ((C m ⊗ C j1) ⊗ (C n ⊗ C j2))
  -> (C (m * n) ⊗ (C j1 ⊗ C j2))
flattenTensorProdCopy v =
  unsafeFromArray @(C (m * n) ⊗ (C j1 ⊗ C j2)) (toArray v :: VS.Vector ℂ)

-- | Entry-wise complex conjugation of a linear map, via 'vectorConjugate' on
-- the map's own 'TensorSpace' structure (a @+>@ map is itself a vector).
-- Antilinear; the single conjugation point for bra formation
-- (memory @conjugation-conventions@).
conjugateMap
  :: ( LinearSpace v, TensorSpace w
     , Scalar v ~ Scalar w )
  => (v +> w) -> (v +> w)
conjugateMap = getAntilinearFunction vectorConjugate
