
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Symmetry.Orphans where



import Control.Category.Constrained (id, (.))
import Math.LinearMap.Category (LinearMap(..), type (⊗), (⊕), InnerSpace ((<.>)), (<.>^), (<$|), euclideanNorm, Norm (Norm), Tensor (Tensor), DualVector, DualSpaceWitness(..), TensorSpace(..), LinearSpace (..), VectorSpace (..), Scalar, AdditiveGroup (..), Semimanifold (..), PseudoAffine (..), type (+>), adjoint, LinearFunction, Bilinear, VSCCoercion (..), getLinearMap)
import Math.OrphanInstances ()
import Linear (V2 (V2), V3 (V3), E (..), V1 (V1))
import Data.Functor.Rep (tabulate, index)
import Control.Lens (Iso', (^.), _1, Ixed (ix), (^?))
import Math.VectorSpace.DimensionAware
import Data.Singletons (Sing, SingI (..), fromSing, sing)
import Data.Singletons.TH (genSingletons)
import qualified Test.QuickCheck as QC
import Prelude hiding ((||), ($), id, (.))
import Math.LinearMap.Asserted
import Data.Complex
import Data.AffineSpace (AffineSpace (..))
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static.Orphans ()
import Control.Arrow.Constrained (($), EnhancedCat (arr), Morphism ((***)))
import Data.Coerce (coerce)
import Data.Type.Coercion (Coercion)
import Unsafe.Coerce (unsafeCoerce)
import GHC.TypeLits (Nat, type (+), KnownNat, SNat, natVal, CmpNat, type (-))
import Linear.V (V, Finite (toV))
import Numeric.LinearAlgebra.Static (R(..), C, L, unrow, vector, M, Sized (fromList, unwrap, create, konst, extract), Domain (dvmap, mul))
import Data.Data (Proxy(..))
import qualified Data.Vector as ArB
import Numeric.LinearAlgebra.HMatrix (Vector, Matrix, Indexable ((!)))
import qualified Numeric.LinearAlgebra as HMat
import qualified Data.Vector.Generic as VG
import Control.Monad.ST (ST)
import Data.Maybe (fromMaybe)
import Data.Function (on)
import qualified Numeric.LinearAlgebra.Static as G
import qualified Control.Category.Constrained as C
import Data.Kind (Type)
import Symmetry.Utils (Z(..), Add(..))


data Z2 = Flip | Id
-- type U1 = Double

data Z2Irreps = Odd | Even
$(genSingletons [''Z2Irreps])
type U1Irreps = Z
type SU2Irreps = Nat

type family U1IrrepDim (p :: U1Irreps) :: Nat where
  U1IrrepDim p = 1

type family Z2IrrepDim (p :: Z2Irreps) :: Nat where
  Z2IrrepDim Odd = 1
  Z2IrrepDim Even = 1

type family SU2IrrepDim (i :: Nat) :: Nat where
  SU2IrrepDim j = j + 1

-- Irreps are static complex vectors; instances mirror @C (dim p)@ but keep phantom labels distinct.

newtype IrrepZ2 (p :: Z2Irreps) = IrrepZ2 { unIrrepZ2 :: C (Z2IrrepDim p) }

newtype IrrepU1 (p :: U1Irreps) = IrrepU1 { unIrrepU1 :: C (U1IrrepDim p) }

newtype IrrepSU2 (j :: SU2Irreps) = IrrepSU2 { unIrrepSU2 :: C (SU2IrrepDim j) }




data Group = U1 | SU2
type family Irreps (g :: Group) :: Type where 
  Irreps U1 = U1Irreps
  Irreps SU2 = SU2Irreps

type IrrepDim :: forall (g :: Group) -> Irreps g -> Nat
type family IrrepDim (g :: Group) (p :: Irreps g) :: Nat where
  IrrepDim U1 p = 1
  IrrepDim SU2 p = p + 1
newtype Irrep (g :: Group) (p :: Irreps g) = Irrep { unGIrrep :: C (IrrepDim g p) }

foo :: Irrep SU2 1
foo = Irrep undefined

deriving newtype instance KnownNat (Z2IrrepDim p) => AdditiveGroup (IrrepZ2 p)

instance KnownNat (Z2IrrepDim p) => VectorSpace (IrrepZ2 p) where
  type Scalar (IrrepZ2 p) = Complex Double
  μ *^ IrrepZ2 v = IrrepZ2 (μ *^ v)

deriving newtype instance KnownNat (Z2IrrepDim p) => InnerSpace (IrrepZ2 p)

deriving newtype instance KnownNat (Z2IrrepDim p) => AffineSpace (IrrepZ2 p)

instance KnownNat (Z2IrrepDim p) => Semimanifold (IrrepZ2 p) where
  type Needle (IrrepZ2 p) = C (Z2IrrepDim p)
  IrrepZ2 v .+~^ δ = IrrepZ2 (v ^+^ δ)

instance KnownNat (Z2IrrepDim p) => PseudoAffine (IrrepZ2 p) where
  IrrepZ2 v .-~! IrrepZ2 w = v ^-^ w
  IrrepZ2 v .-~. IrrepZ2 w = Just (v ^-^ w)

instance KnownNat (Z2IrrepDim p) => DimensionAware (IrrepZ2 p) where
  type StaticDimension (IrrepZ2 p) = 'Just (Z2IrrepDim p)
  dimensionalityWitness = IsStaticDimensional

instance (KnownNat n, n ~ Z2IrrepDim p) => n `Dimensional` IrrepZ2 p where
  knownDimensionalitySing = sing
  unsafeFromArrayWithOffset i ar = IrrepZ2 (unsafeFromArrayWithOffset i ar)
  unsafeWriteArrayWithOffset ar i (IrrepZ2 v) = unsafeWriteArrayWithOffset ar i v



instance (KnownNat (Z2IrrepDim p), Scalar (IrrepZ2 p) ~ Complex Double) => TensorSpace (IrrepZ2 p) where
  type TensorProduct (IrrepZ2 p) w = TensorProduct (C (Z2IrrepDim p)) w
  scalarSpaceWitness = undefined -- unsafeCoerce (scalarSpaceWitness @(C (Z2IrrepDim p)))
  linearManifoldWitness = undefined -- unsafeCoerce (linearManifoldWitness @(C 1))
  zeroTensor :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepZ2 p), Scalar w ~ Complex Double) => IrrepZ2 p ⊗ w
  zeroTensor = undefined -- unsafeCoerce (c1ZeroTensor @w)
  addTensors :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepZ2 p), Scalar w ~ Complex Double) => (IrrepZ2 p ⊗ w) -> (IrrepZ2 p ⊗ w) -> IrrepZ2 p ⊗ w
  addTensors tx ty = undefined -- unsafeCoerce (c1AddTensors @w (unsafeCoerce tx) (unsafeCoerce ty))
  subtractTensors :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepZ2 p), Scalar w ~ Complex Double) => (IrrepZ2 p ⊗ w) -> (IrrepZ2 p ⊗ w) -> IrrepZ2 p ⊗ w
  subtractTensors tx ty = undefined -- unsafeCoerce (c1SubtractTensors @w (unsafeCoerce tx) (unsafeCoerce ty))
  negateTensor :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepZ2 p), Scalar w ~ Complex Double) => (IrrepZ2 p ⊗ w) -+> (IrrepZ2 p ⊗ w)
  negateTensor = undefined -- unsafeCoerce (c1NegateTensor @w)
  scaleTensor :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepZ2 p), Scalar w ~ Complex Double) => Bilinear (Complex Double) (IrrepZ2 p ⊗ w) (IrrepZ2 p ⊗ w)
  scaleTensor = undefined -- unsafeCoerce (c1ScaleTensor @w)
  toFlatTensor :: IrrepZ2 p -+> (IrrepZ2 p ⊗ Scalar (IrrepZ2 p))
  toFlatTensor = undefined -- unsafeCoerce c1ToFlatTensor
  fromFlatTensor :: (IrrepZ2 p ⊗ Scalar (IrrepZ2 p)) -+> IrrepZ2 p
  fromFlatTensor = undefined -- unsafeCoerce c1FromFlatTensor
  tensorProduct :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepZ2 p), Scalar w ~ Complex Double) => Bilinear (IrrepZ2 p) w (IrrepZ2 p ⊗ w)
  tensorProduct = undefined -- unsafeCoerce (c1TensorProduct @w)
  transposeTensor :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepZ2 p), Scalar w ~ Complex Double) => (IrrepZ2 p ⊗ w) -+> (w ⊗ IrrepZ2 p)
  transposeTensor = undefined -- unsafeCoerce (c1TransposeTensor @w)
  -- fmapTensor ::
  --   forall w x.
  --   ( TensorSpace w, Scalar w ~ Scalar (IrrepZ2 p), Scalar w ~ Complex Double
  --   , TensorSpace x, Scalar x ~ Scalar (IrrepZ2 p), Scalar x ~ Complex Double) =>
  --   Bilinear (x-+>w) (IrrepZ2 p ⊗ x) (IrrepZ2 p ⊗ w)
  fmapTensor = undefined -- unsafeCoerce (c1FmapTensor @x @w)
  fzipTensorWith ::
    forall w x y.
    ( TensorSpace w, Scalar w ~ Scalar (IrrepZ2 p), Scalar w ~ Complex Double
    , TensorSpace x, Scalar x ~ Scalar (IrrepZ2 p), Scalar x ~ Complex Double
    , TensorSpace y, Scalar y ~ Scalar (IrrepZ2 p), Scalar y ~ Complex Double) =>
    Bilinear ((x, y) -+> w) (IrrepZ2 p ⊗ x, IrrepZ2 p ⊗ y) (IrrepZ2 p ⊗ w)
  fzipTensorWith = undefined -- unsafeCoerce (c1FzipTensorWith @w @x @y)
  coerceFmapTensorProduct ::
    forall a b functor.
    ( Functor functor
    , TensorSpace a, Scalar a ~ Scalar (IrrepZ2 p)
    , TensorSpace b, Scalar b ~ Scalar (IrrepZ2 p)) =>
    functor (IrrepZ2 p) ->
    VSCCoercion (Scalar (IrrepZ2 p)) a b ->
    Coercion (TensorProduct (IrrepZ2 p) a) (TensorProduct (IrrepZ2 p) b)
  coerceFmapTensorProduct fv vsc = undefined 
  wellDefinedVector (IrrepZ2 v) = IrrepZ2 <$> wellDefinedVector v
  wellDefinedTensor :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepZ2 p), Scalar w ~ Complex Double) => (IrrepZ2 p ⊗ w) -> Maybe (IrrepZ2 p ⊗ w)
  wellDefinedTensor t = undefined -- unsafeCoerce (c1WellDefinedTensor @w (unsafeCoerce t))
  vectorConjugate = undefined -- unsafeCoerce (vectorConjugate @(C 1))
  tensorUnsafeFromArrayWithOffset ::
    forall w n m α.
    ( n `Dimensional` IrrepZ2 p
    , TensorSpace w, m `Dimensional` w
    , Scalar w ~ Scalar (IrrepZ2 p), Scalar w ~ Complex Double
    , VG.Vector α (Complex Double)) =>
    Int -> α (Complex Double) -> Tensor (Complex Double) (IrrepZ2 p) w
  tensorUnsafeFromArrayWithOffset i ar =
    undefined -- unsafeCoerce (tensorUnsafeFromArrayWithOffset @(C (Z2IrrepDim p)) @w @α @n @m i ar :: Tensor (Complex Double) (C (Z2IrrepDim p)) w)
  tensorUnsafeWriteArrayWithOffset ::
    forall w n m α σ.
    ( n `Dimensional` IrrepZ2 p
    , TensorSpace w, m `Dimensional` w
    , Scalar w ~ Scalar (IrrepZ2 p), Scalar w ~ Complex Double
    , VG.Vector α (Complex Double)) =>
    VG.Mutable α σ (Complex Double) -> Int -> Tensor (Complex Double) (IrrepZ2 p) w -> ST σ ()
  tensorUnsafeWriteArrayWithOffset ar i t =
    undefined -- tensorUnsafeWriteArrayWithOffset @(C (Z2IrrepDim p)) @w @α @σ @n @m ar i (unsafeCoerce t :: Tensor (Complex Double) (C (Z2IrrepDim p)) w)

instance (KnownNat (Z2IrrepDim p), Scalar (IrrepZ2 p) ~ Complex Double) => LinearSpace (IrrepZ2 p) where
  type DualVector (IrrepZ2 p) = IrrepZ2 p
  dualSpaceWitness = DualSpaceWitness
  linearId = undefined -- unsafeCoerce (linearId :: LinearMap (Complex Double) (C 1) (C 1))
  applyDualVector = undefined -- unsafeCoerce (applyDualVector :: Bilinear (DualVector (C 1)) (C 1) (Complex Double))
  applyLinear ::
    forall w.
    (TensorSpace w, Scalar w ~ Scalar (IrrepZ2 p), Scalar w ~ Complex Double) =>
    Bilinear (LinearMap (Complex Double) (IrrepZ2 p) w) (IrrepZ2 p) w
  applyLinear = undefined -- unsafeCoerce (c1ApplyLinear @w)
  tensorId ::
    forall w.
    (LinearSpace w, Scalar w ~ Scalar (IrrepZ2 p), Scalar w ~ Complex Double) =>
    LinearMap (Complex Double) (IrrepZ2 p ⊗ w) (IrrepZ2 p ⊗ w)
  tensorId = undefined -- unsafeCoerce (c1TensorId @w)
  applyTensorFunctional ::
    forall u.
    (LinearSpace u, Scalar u ~ Scalar (IrrepZ2 p), Scalar u ~ Complex Double) =>
    Bilinear (LinearMap (Complex Double) (IrrepZ2 p) (DualVector u)) (Tensor (Complex Double) (IrrepZ2 p) u) (Complex Double)
  applyTensorFunctional = undefined -- unsafeCoerce (c1ApplyTensorFunctional @u)
  applyTensorLinMap ::
    forall u w.
    ( LinearSpace u, Scalar u ~ Scalar (IrrepZ2 p), Scalar u ~ Complex Double
    , TensorSpace w, Scalar w ~ Scalar (IrrepZ2 p), Scalar w ~ Complex Double) =>
    Bilinear (LinearMap (Complex Double) (Tensor (Complex Double) (IrrepZ2 p) u) w) (Tensor (Complex Double) (IrrepZ2 p) u) w
  applyTensorLinMap = undefined -- unsafeCoerce (c1ApplyTensorLinMap @u @w)
  composeLinear ::
    forall w x.
    ( LinearSpace w, Scalar w ~ Scalar (IrrepZ2 p), Scalar w ~ Complex Double
    , TensorSpace x, Scalar x ~ Scalar (IrrepZ2 p), Scalar x ~ Complex Double) =>
    Bilinear (LinearMap (Complex Double) w x) (LinearMap (Complex Double) (IrrepZ2 p) w) (LinearMap (Complex Double) (IrrepZ2 p) x)
  composeLinear = undefined -- unsafeCoerce (c1ComposeLinear @w @x)
  contractTensorMap ::
    forall w.
    (TensorSpace w, Scalar w ~ Scalar (IrrepZ2 p), Scalar w ~ Complex Double) =>
    LinearFunction (Complex Double) (LinearMap (Complex Double) (IrrepZ2 p) (IrrepZ2 p ⊗ w)) w
  contractTensorMap = undefined -- unsafeCoerce (c1ContractTensorMap @w)
  contractLinearMapAgainstTensorLookup ::
    forall w x u.
    ( TensorSpace w, Scalar w ~ Scalar (IrrepZ2 p), Scalar w ~ Complex Double
    , TensorSpace x, Scalar x ~ Scalar (IrrepZ2 p), Scalar x ~ Complex Double
    , TensorSpace u, Scalar u ~ Scalar (IrrepZ2 p), Scalar u ~ Complex Double) =>
    LinearFunction
      (Complex Double)
      (LinearFunction (Complex Double) (LinearFunction (Complex Double) (Tensor (Complex Double) (IrrepZ2 p) x) x) (LinearFunction (Complex Double) w u))
      (LinearFunction (Complex Double) (LinearMap (Complex Double) (IrrepZ2 p) w) u)
  contractLinearMapAgainstTensorLookup =
    undefined -- unsafeCoerce (c1ContractLinearMapAgainstTensorLookup @x @w @u)
  useTupleLinearSpaceComponents _ = undefined

deriving newtype instance KnownNat (Z2IrrepDim p) => Eq (IrrepZ2 p)

deriving newtype instance KnownNat (Z2IrrepDim p) => Show (IrrepZ2 p)

deriving newtype instance KnownNat (Z2IrrepDim p) => Num (IrrepZ2 p)

deriving newtype instance KnownNat (Z2IrrepDim p) => Fractional (IrrepZ2 p)

deriving newtype instance KnownNat (Z2IrrepDim p) => Floating (IrrepZ2 p)

-- | U(1) irreps: phantom charge @p@ distinguishes @IrrepU1 1@ from @IrrepU1 2@ at type level.

deriving newtype instance KnownNat (U1IrrepDim p) => AdditiveGroup (IrrepU1 p)

instance KnownNat (U1IrrepDim p) => VectorSpace (IrrepU1 p) where
  type Scalar (IrrepU1 p) = Complex Double
  μ *^ IrrepU1 v = IrrepU1 (μ *^ v)

deriving newtype instance KnownNat (U1IrrepDim p) => InnerSpace (IrrepU1 p)

deriving newtype instance KnownNat (U1IrrepDim p) => AffineSpace (IrrepU1 p)

instance KnownNat (U1IrrepDim p) => Semimanifold (IrrepU1 p) where
  type Needle (IrrepU1 p) = C 1
  IrrepU1 v .+~^ δ = IrrepU1 (v ^+^ δ)

instance KnownNat (U1IrrepDim p) => PseudoAffine (IrrepU1 p) where
  IrrepU1 v .-~! IrrepU1 w = v ^-^ w
  IrrepU1 v .-~. IrrepU1 w = Just (v ^-^ w)

instance KnownNat (U1IrrepDim p) => DimensionAware (IrrepU1 p) where
  type StaticDimension (IrrepU1 p) = 'Just 1
  dimensionalityWitness = IsStaticDimensional

instance KnownNat (U1IrrepDim p) => 1 `Dimensional` IrrepU1 p where
  knownDimensionalitySing = sing
  unsafeFromArrayWithOffset i ar = IrrepU1 (unsafeFromArrayWithOffset i ar)
  unsafeWriteArrayWithOffset ar i (IrrepU1 v) = unsafeWriteArrayWithOffset ar i v

-- instance AdditiveGroup w => AdditiveGroup (TensorU1 ( p) (w :: Type)) where
--   zeroV = undefined
--   (^+^) = undefined
--   (^-^) = undefined
--   negateV = undefined

-- type family TensorU1 (p :: U1Irreps) (w :: Type) :: Type where
--   TensorU1 p (IrrepU1 q) =
--     IrrepU1 (Add p q)

--   TensorU1 p w = TensorProduct (C (U1IrrepDim p)) w

type TensorU1 p w =
  TensorU1Pack p (IsIrrepU1 w) w

-- class ZeroTensorU1 (p :: U1Irreps) (w :: Type) where
--   zeroTensorU1 :: TensorU1 p w

-- instance {-# OVERLAPPING #-}
--   KnownNat (U1IrrepDim (Add p q))
--   => ZeroTensorU1 p (IrrepU1 q)
--   where

--   zeroTensorU1 =
--     IrrepU1 zeroV

-- instance {-# OVERLAPPING #-}
--   ( TensorSpace w, 
--   TensorU1 p w ~ Tensor (Complex Double) (C 1) w,
--   Scalar w ~ Complex Double
--   , Scalar (C (U1IrrepDim p)) ~ Complex Double
--   )
--   => ZeroTensorU1 p w
--   where

--   zeroTensorU1 =
--     zeroTensor @(C (U1IrrepDim p)) @w

type family IsIrrepU1 (w :: Type) :: Maybe U1Irreps where
  IsIrrepU1 (IrrepU1 q) = 'Just q
  IsIrrepU1 w           = 'Nothing

type family TensorU1Pack
  (p :: U1Irreps)
  (mw :: Maybe U1Irreps)
  (w :: Type)
  :: Type where

  TensorU1Pack p ('Just q) w =
    IrrepU1 (Add p q)

  TensorU1Pack p 'Nothing w =
    TensorProduct (C (U1IrrepDim p)) w

data IrrepU1Case (mw :: Maybe U1Irreps) where
  IsIrrepU1Case  :: IrrepU1Case ('Just q)
  NotIrrepU1Case :: IrrepU1Case 'Nothing

class KnownIrrepU1Case w where
  irrepU1Case :: IrrepU1Case (IsIrrepU1 w)

instance KnownIrrepU1Case (IrrepU1 q) where
  irrepU1Case = IsIrrepU1Case

-- instance {-# OVERLAPPABLE #-} KnownIrrepU1Case w where
--   irrepU1Case :: IrrepU1Case (IsIrrepU1 w)
--   irrepU1Case = NotIrrepU1Case

instance(KnownNat (U1IrrepDim p), Scalar (IrrepU1 p) ~ Complex Double) => TensorSpace (IrrepU1 p) where
  type TensorProduct (IrrepU1 p) w = TensorU1 p w
  scalarSpaceWitness = undefined -- unsafeCoerce (scalarSpaceWitness @(C (U1IrrepDim p)))
  linearManifoldWitness = undefined -- unsafeCoerce (linearManifoldWitness @(C (U1IrrepDim p)))
  zeroTensor :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepU1 p), Scalar w ~ Complex Double) => IrrepU1 p ⊗ w
  zeroTensor = undefined
    -- case irrepU1Case @w of
    --   IsIrrepU1Case ->
    --     IrrepU1 undefined

      -- NotIrrepU1Case ->
      --   zeroTensor @(C (U1IrrepDim p)) @w

  addTensors :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepU1 p), Scalar w ~ Complex Double) => (IrrepU1 p ⊗ w) -> (IrrepU1 p ⊗ w) -> IrrepU1 p ⊗ w
  addTensors tx ty = undefined -- unsafeCoerce (c1AddTensors @w (unsafeCoerce tx) (unsafeCoerce ty))
  subtractTensors :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepU1 p), Scalar w ~ Complex Double) => (IrrepU1 p ⊗ w) -> (IrrepU1 p ⊗ w) -> IrrepU1 p ⊗ w
  subtractTensors tx ty = undefined -- unsafeCoerce (c1SubtractTensors @w (unsafeCoerce tx) (unsafeCoerce ty))
  negateTensor :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepU1 p), Scalar w ~ Complex Double) => (IrrepU1 p ⊗ w) -+> (IrrepU1 p ⊗ w)
  negateTensor = undefined -- unsafeCoerce (c1NegateTensor @w)
  scaleTensor :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepU1 p), Scalar w ~ Complex Double) => Bilinear (Complex Double) (IrrepU1 p ⊗ w) (IrrepU1 p ⊗ w)
  scaleTensor = undefined -- unsafeCoerce (c1ScaleTensor @w)
  toFlatTensor :: IrrepU1 p -+> (IrrepU1 p ⊗ Scalar (IrrepU1 p))
  toFlatTensor = undefined -- unsafeCoerce c1ToFlatTensor
  fromFlatTensor :: (IrrepU1 p ⊗ Scalar (IrrepU1 p)) -+> IrrepU1 p
  fromFlatTensor = undefined -- unsafeCoerce c1FromFlatTensor
  tensorProduct :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepU1 p), Scalar w ~ Complex Double) => Bilinear (IrrepU1 p) w (IrrepU1 p ⊗ w)
  tensorProduct = undefined -- unsafeCoerce (c1TensorProduct @w)
  transposeTensor :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepU1 p), Scalar w ~ Complex Double) => (IrrepU1 p ⊗ w) -+> (w ⊗ IrrepU1 p)
  transposeTensor = undefined -- unsafeCoerce (c1TransposeTensor @w)
  -- fmapTensor ::
  --   forall w x.
  --   ( TensorSpace w, Scalar w ~ Scalar (IrrepU1 p), Scalar w ~ Complex Double
  --   , TensorSpace x, Scalar x ~ Scalar (IrrepU1 p), Scalar x ~ Complex Double) =>
  --   Bilinear (x-+>w) (IrrepU1 p ⊗ x) (IrrepU1 p ⊗ w)
  fmapTensor = undefined -- unsafeCoerce (c1FmapTensor @x @w)
  fzipTensorWith ::
    forall w x y.
    ( TensorSpace w, Scalar w ~ Scalar (IrrepU1 p), Scalar w ~ Complex Double
    , TensorSpace x, Scalar x ~ Scalar (IrrepU1 p), Scalar x ~ Complex Double
    , TensorSpace y, Scalar y ~ Scalar (IrrepU1 p), Scalar y ~ Complex Double) =>
    Bilinear ((x, y) -+> w) (IrrepU1 p ⊗ x, IrrepU1 p ⊗ y) (IrrepU1 p ⊗ w)
  fzipTensorWith = undefined -- unsafeCoerce (c1FzipTensorWith @w @x @y)
  coerceFmapTensorProduct ::
    forall a b functor.
    ( Functor functor
    , TensorSpace a, Scalar a ~ Scalar (IrrepU1 p)
    , TensorSpace b, Scalar b ~ Scalar (IrrepU1 p)) =>
    functor (IrrepU1 p) ->
    VSCCoercion (Scalar (IrrepU1 p)) a b ->
    Coercion (TensorProduct (IrrepU1 p) a) (TensorProduct (IrrepU1 p) b)
  coerceFmapTensorProduct fv vsc =
    undefined -- unsafeCoerce (c1CoerceFmapTensorProduct (unsafeCoerce fv :: functor (C 1)) vsc)
  wellDefinedVector (IrrepU1 v) = IrrepU1 <$> wellDefinedVector v
  wellDefinedTensor :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepU1 p), Scalar w ~ Complex Double) => (IrrepU1 p ⊗ w) -> Maybe (IrrepU1 p ⊗ w)
  wellDefinedTensor t = undefined -- unsafeCoerce (c1WellDefinedTensor @w (unsafeCoerce t))
  vectorConjugate = undefined -- unsafeCoerce (vectorConjugate @(C 1))
  tensorUnsafeFromArrayWithOffset ::
    forall w n m α.
    ( n `Dimensional` IrrepU1 p
    , TensorSpace w, m `Dimensional` w
    , Scalar w ~ Scalar (IrrepU1 p), Scalar w ~ Complex Double
    , VG.Vector α (Complex Double)) =>
    Int -> α (Complex Double) -> Tensor (Complex Double) (IrrepU1 p) w
  tensorUnsafeFromArrayWithOffset i ar =
    undefined -- unsafeCoerce (tensorUnsafeFromArrayWithOffset @(C (U1IrrepDim p)) @w @α @n @m i ar :: Tensor (Complex Double) (C (U1IrrepDim p)) w)
  tensorUnsafeWriteArrayWithOffset ::
    forall w n m α σ.
    ( n `Dimensional` IrrepU1 p
    , TensorSpace w, m `Dimensional` w
    , Scalar w ~ Scalar (IrrepU1 p), Scalar w ~ Complex Double
    , VG.Vector α (Complex Double)) =>
    VG.Mutable α σ (Complex Double) -> Int -> Tensor (Complex Double) (IrrepU1 p) w -> ST σ ()
  tensorUnsafeWriteArrayWithOffset ar i t =
    undefined -- unsafeCoerce (tensorUnsafeWriteArrayWithOffset @(C (U1IrrepDim p)) @w @α @σ @n @m ar i (unsafeCoerce t :: Tensor (Complex Double) (C (U1IrrepDim p)) w))

instance (KnownNat (U1IrrepDim p), Scalar (IrrepU1 p) ~ Complex Double) => LinearSpace (IrrepU1 p) where
  type DualVector (IrrepU1 p) = IrrepU1 p
  dualSpaceWitness = DualSpaceWitness
  linearId = undefined -- unsafeCoerce (linearId :: LinearMap (Complex Double) (C (U1IrrepDim p)) (C (U1IrrepDim p)))
  applyDualVector = undefined -- unsafeCoerce (applyDualVector :: Bilinear (DualVector (C (U1IrrepDim p))) (C (U1IrrepDim p)) (Complex Double))
  applyLinear ::
    forall w.
    (TensorSpace w, Scalar w ~ Scalar (IrrepU1 p), Scalar w ~ Complex Double) =>
    Bilinear (LinearMap (Complex Double) (IrrepU1 p) w) (IrrepU1 p) w
  applyLinear = undefined -- unsafeCoerce (c1ApplyLinear @w)
  tensorId ::
    forall w.
    (LinearSpace w, Scalar w ~ Scalar (IrrepU1 p), Scalar w ~ Complex Double) =>
    LinearMap (Complex Double) (IrrepU1 p ⊗ w) (IrrepU1 p ⊗ w)
  tensorId = undefined -- unsafeCoerce (c1TensorId @w)
  applyTensorFunctional ::
    forall u.
    (LinearSpace u, Scalar u ~ Scalar (IrrepU1 p), Scalar u ~ Complex Double) =>
    Bilinear (LinearMap (Complex Double) (IrrepU1 p) (DualVector u)) (Tensor (Complex Double) (IrrepU1 p) u) (Complex Double)
  applyTensorFunctional = undefined -- unsafeCoerce (c1ApplyTensorFunctional @u)
  applyTensorLinMap ::
    forall u w.
    ( LinearSpace u, Scalar u ~ Scalar (IrrepU1 p), Scalar u ~ Complex Double
    , TensorSpace w, Scalar w ~ Scalar (IrrepU1 p), Scalar w ~ Complex Double) =>
    Bilinear (LinearMap (Complex Double) (Tensor (Complex Double) (IrrepU1 p) u) w) (Tensor (Complex Double) (IrrepU1 p) u) w
  applyTensorLinMap = undefined -- unsafeCoerce (c1ApplyTensorLinMap @u @w)
  composeLinear ::
    forall w x.
    ( LinearSpace w, Scalar w ~ Scalar (IrrepU1 p), Scalar w ~ Complex Double
    , TensorSpace x, Scalar x ~ Scalar (IrrepU1 p), Scalar x ~ Complex Double) =>
    Bilinear (LinearMap (Complex Double) w x) (LinearMap (Complex Double) (IrrepU1 p) w) (LinearMap (Complex Double) (IrrepU1 p) x)
  composeLinear = undefined -- unsafeCoerce (c1ComposeLinear @w @x)
  contractTensorMap ::
    forall w.
    (TensorSpace w, Scalar w ~ Scalar (IrrepU1 p), Scalar w ~ Complex Double) =>
    LinearFunction (Complex Double) (LinearMap (Complex Double) (IrrepU1 p) (IrrepU1 p ⊗ w)) w
  contractTensorMap = undefined -- unsafeCoerce (c1ContractTensorMap @w)
  contractLinearMapAgainstTensorLookup ::
    forall w x u.
    ( TensorSpace w, Scalar w ~ Scalar (IrrepU1 p), Scalar w ~ Complex Double
    , TensorSpace x, Scalar x ~ Scalar (IrrepU1 p), Scalar x ~ Complex Double
    , TensorSpace u, Scalar u ~ Scalar (IrrepU1 p), Scalar u ~ Complex Double) =>
    LinearFunction
      (Complex Double)
      (LinearFunction (Complex Double) (LinearFunction (Complex Double) (Tensor (Complex Double) (IrrepU1 p) x) x) (LinearFunction (Complex Double) w u))
      (LinearFunction (Complex Double) (LinearMap (Complex Double) (IrrepU1 p) w) u)
  contractLinearMapAgainstTensorLookup =
    undefined -- unsafeCoerce (c1ContractLinearMapAgainstTensorLookup @x @w @u)
  useTupleLinearSpaceComponents _ = undefined

deriving newtype instance KnownNat (U1IrrepDim p) => Eq (IrrepU1 p)

deriving newtype instance KnownNat (U1IrrepDim p) => Show (IrrepU1 p)

deriving newtype instance KnownNat (U1IrrepDim p) => Num (IrrepU1 p)

deriving newtype instance KnownNat (U1IrrepDim p) => Fractional (IrrepU1 p)

deriving newtype instance KnownNat (U1IrrepDim p) => Floating (IrrepU1 p)

-- | SU(2)-labelled irreps (currently one-dimensional placeholders).

-- deriving newtype instance KnownNat (SU2IrrepDim i j) => AdditiveGroup (IrrepSU2 i j)

-- instance KnownNat (SU2IrrepDim i j) => VectorSpace (IrrepSU2 i j) where
--   type Scalar (IrrepSU2 i j) = Complex Double
--   μ *^ IrrepSU2 v = IrrepSU2 (μ *^ v)

-- deriving newtype instance KnownNat (SU2IrrepDim i j) => InnerSpace (IrrepSU2 i j)

-- deriving newtype instance KnownNat (SU2IrrepDim i j) => AffineSpace (IrrepSU2 i j)

-- instance KnownNat (SU2IrrepDim i j) => Semimanifold (IrrepSU2 i j) where
--   type Needle (IrrepSU2 i j) = C 1
--   IrrepSU2 v .+~^ δ = IrrepSU2 (v ^+^ δ)

-- instance KnownNat (SU2IrrepDim i j) => PseudoAffine (IrrepSU2 i j) where
--   IrrepSU2 v .-~! IrrepSU2 w = v ^-^ w
--   IrrepSU2 v .-~. IrrepSU2 w = Just (v ^-^ w)

-- instance KnownNat (SU2IrrepDim i j) => DimensionAware (IrrepSU2 i j) where
--   type StaticDimension (IrrepSU2 i j) = 'Just 1
--   dimensionalityWitness = IsStaticDimensional

-- instance KnownNat (SU2IrrepDim i j) => 1 `Dimensional` IrrepSU2 i j where
--   knownDimensionalitySing = sing
--   unsafeFromArrayWithOffset i ar = IrrepSU2 (unsafeFromArrayWithOffset i ar)
--   unsafeWriteArrayWithOffset ar i (IrrepSU2 v) = unsafeWriteArrayWithOffset ar i v

-- instance (KnownNat (SU2IrrepDim i j), Scalar (IrrepSU2 i j) ~ Complex Double) => TensorSpace (IrrepSU2 i j) where
--   type TensorProduct (IrrepSU2 i j) w = TensorProduct (C 1) w
--   scalarSpaceWitness = undefined -- unsafeCoerce (scalarSpaceWitness @(C 1))
--   linearManifoldWitness = undefined -- unsafeCoerce (linearManifoldWitness @(C 1))
--   zeroTensor :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepSU2 i j), Scalar w ~ Complex Double) => IrrepSU2 i j ⊗ w
--   zeroTensor = undefined -- unsafeCoerce (c1ZeroTensor @w)
--   addTensors :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepSU2 i j), Scalar w ~ Complex Double) => (IrrepSU2 i j ⊗ w) -> (IrrepSU2 i j ⊗ w) -> IrrepSU2 i j ⊗ w
--   addTensors tx ty = undefined -- unsafeCoerce (c1AddTensors @w (unsafeCoerce tx) (unsafeCoerce ty))
--   subtractTensors :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepSU2 i j), Scalar w ~ Complex Double) => (IrrepSU2 i j ⊗ w) -> (IrrepSU2 i j ⊗ w) -> IrrepSU2 i j ⊗ w
--   subtractTensors tx ty = undefined -- unsafeCoerce (c1SubtractTensors @w (unsafeCoerce tx) (unsafeCoerce ty))
--   negateTensor :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepSU2 i j), Scalar w ~ Complex Double) => (IrrepSU2 i j ⊗ w) -+> (IrrepSU2 i j ⊗ w)
--   negateTensor = undefined -- unsafeCoerce (c1NegateTensor @w)
--   scaleTensor :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepSU2 i j), Scalar w ~ Complex Double) => Bilinear (Complex Double) (IrrepSU2 i j ⊗ w) (IrrepSU2 i j ⊗ w)
--   scaleTensor = undefined -- unsafeCoerce (c1ScaleTensor @w)
--   toFlatTensor :: IrrepSU2 i j -+> (IrrepSU2 i j ⊗ Scalar (IrrepSU2 i j))
--   toFlatTensor = undefined -- unsafeCoerce c1ToFlatTensor
--   fromFlatTensor :: (IrrepSU2 i j ⊗ Scalar (IrrepSU2 i j)) -+> IrrepSU2 i j
--   fromFlatTensor = undefined -- unsafeCoerce c1FromFlatTensor
--   tensorProduct :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepSU2 i j), Scalar w ~ Complex Double) => Bilinear (IrrepSU2 i j) w (IrrepSU2 i j ⊗ w)
--   tensorProduct = undefined -- unsafeCoerce (c1TensorProduct @w)
--   transposeTensor :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepSU2 i j), Scalar w ~ Complex Double) => (IrrepSU2 i j ⊗ w) -+> (w ⊗ IrrepSU2 i j)
--   transposeTensor = undefined -- unsafeCoerce (c1TransposeTensor @w)
--   fmapTensor ::
--     forall w x.
--     ( TensorSpace w, Scalar w ~ Scalar (IrrepSU2 i j), Scalar w ~ Complex Double
--     , TensorSpace x, Scalar x ~ Scalar (IrrepSU2 i j), Scalar x ~ Complex Double) =>
--     Bilinear (x-+>w) (IrrepSU2 i j ⊗ x) (IrrepSU2 i j ⊗ w)
--   fmapTensor = undefined -- unsafeCoerce (c1FmapTensor @x @w)
--   fzipTensorWith ::
--     forall w x y.
--     ( TensorSpace w, Scalar w ~ Scalar (IrrepSU2 i j), Scalar w ~ Complex Double
--     , TensorSpace x, Scalar x ~ Scalar (IrrepSU2 i j), Scalar x ~ Complex Double
--     , TensorSpace y, Scalar y ~ Scalar (IrrepSU2 i j), Scalar y ~ Complex Double) =>
--     Bilinear ((x, y) -+> w) (IrrepSU2 i j ⊗ x, IrrepSU2 i j ⊗ y) (IrrepSU2 i j ⊗ w)
--   fzipTensorWith = undefined -- unsafeCoerce (c1FzipTensorWith @w @x @y)
--   coerceFmapTensorProduct ::
--     forall a b functor.
--     ( Functor functor
--     , TensorSpace a, Scalar a ~ Scalar (IrrepSU2 i j)
--     , TensorSpace b, Scalar b ~ Scalar (IrrepSU2 i j)) =>
--     functor (IrrepSU2 i j) ->
--     VSCCoercion (Scalar (IrrepSU2 i j)) a b ->
--     Coercion (TensorProduct (IrrepSU2 i j) a) (TensorProduct (IrrepSU2 i j) b)
--   coerceFmapTensorProduct fv vsc =
--     unsafeCoerce (c1CoerceFmapTensorProduct (unsafeCoerce fv :: functor (C 1)) vsc)
--   wellDefinedVector (IrrepSU2 v) = IrrepSU2 <$> wellDefinedVector v
--   wellDefinedTensor :: forall w. (TensorSpace w, Scalar w ~ Scalar (IrrepSU2 i j), Scalar w ~ Complex Double) => (IrrepSU2 i j ⊗ w) -> Maybe (IrrepSU2 i j ⊗ w)
--   wellDefinedTensor t = undefined -- unsafeCoerce (c1WellDefinedTensor @w (unsafeCoerce t))
--   vectorConjugate = undefined -- unsafeCoerce (vectorConjugate @(C 1))
--   tensorUnsafeFromArrayWithOffset ::
--     forall w n m α.
--     ( n `Dimensional` IrrepSU2 i j
--     , TensorSpace w, m `Dimensional` w
--     , Scalar w ~ Scalar (IrrepSU2 i j), Scalar w ~ Complex Double
--     , VG.Vector α (Complex Double)) =>
--     Int -> α (Complex Double) -> Tensor (Complex Double) (IrrepSU2 i j) w
--   tensorUnsafeFromArrayWithOffset i ar =
--     unsafeCoerce (tensorUnsafeFromArrayWithOffset @(C 1) @w @α @n @m i ar :: Tensor (Complex Double) (C 1) w)
--   tensorUnsafeWriteArrayWithOffset ::
--     forall w n m α σ.
--     ( n `Dimensional` IrrepSU2 i j
--     , TensorSpace w, m `Dimensional` w
--     , Scalar w ~ Scalar (IrrepSU2 i j), Scalar w ~ Complex Double
--     , VG.Vector α (Complex Double)) =>
--     VG.Mutable α σ (Complex Double) -> Int -> Tensor (Complex Double) (IrrepSU2 i j) w -> ST σ ()
--   tensorUnsafeWriteArrayWithOffset ar i t =
--     tensorUnsafeWriteArrayWithOffset @(C 1) @w @α @σ @n @m ar i (unsafeCoerce t :: Tensor (Complex Double) (C 1) w)

-- instance (KnownNat (SU2IrrepDim i j), Scalar (IrrepSU2 i j) ~ Complex Double) => LinearSpace (IrrepSU2 i j) where
--   type DualVector (IrrepSU2 i j) = IrrepSU2 i j
--   dualSpaceWitness = DualSpaceWitness
--   linearId = undefined -- unsafeCoerce (linearId :: LinearMap (Complex Double) (C 1) (C 1))
--   applyDualVector = undefined -- unsafeCoerce (applyDualVector :: Bilinear (DualVector (C 1)) (C 1) (Complex Double))
--   applyLinear ::
--     forall w.
--     (TensorSpace w, Scalar w ~ Scalar (IrrepSU2 i j), Scalar w ~ Complex Double) =>
--     Bilinear (LinearMap (Complex Double) (IrrepSU2 i j) w) (IrrepSU2 i j) w
--   applyLinear = undefined -- unsafeCoerce (c1ApplyLinear @w)
--   tensorId ::
--     forall w.
--     (LinearSpace w, Scalar w ~ Scalar (IrrepSU2 i j), Scalar w ~ Complex Double) =>
--     LinearMap (Complex Double) (IrrepSU2 i j ⊗ w) (IrrepSU2 i j ⊗ w)
--   tensorId = undefined -- unsafeCoerce (c1TensorId @w)
--   applyTensorFunctional ::
--     forall u.
--     (LinearSpace u, Scalar u ~ Scalar (IrrepSU2 i j), Scalar u ~ Complex Double) =>
--     Bilinear (LinearMap (Complex Double) (IrrepSU2 i j) (DualVector u)) (Tensor (Complex Double) (IrrepSU2 i j) u) (Complex Double)
--   applyTensorFunctional = undefined -- unsafeCoerce (c1ApplyTensorFunctional @u)
--   applyTensorLinMap ::
--     forall u w.
--     ( LinearSpace u, Scalar u ~ Scalar (IrrepSU2 i j), Scalar u ~ Complex Double
--     , TensorSpace w, Scalar w ~ Scalar (IrrepSU2 i j), Scalar w ~ Complex Double) =>
--     Bilinear (LinearMap (Complex Double) (Tensor (Complex Double) (IrrepSU2 i j) u) w) (Tensor (Complex Double) (IrrepSU2 i j) u) w
--   applyTensorLinMap = undefined -- unsafeCoerce (c1ApplyTensorLinMap @u @w)
--   composeLinear ::
--     forall w x.
--     ( LinearSpace w, Scalar w ~ Scalar (IrrepSU2 i j), Scalar w ~ Complex Double
--     , TensorSpace x, Scalar x ~ Scalar (IrrepSU2 i j), Scalar x ~ Complex Double) =>
--     Bilinear (LinearMap (Complex Double) w x) (LinearMap (Complex Double) (IrrepSU2 i j) w) (LinearMap (Complex Double) (IrrepSU2 i j) x)
--   composeLinear = undefined -- unsafeCoerce (c1ComposeLinear @w @x)
--   contractTensorMap ::
--     forall w.
--     (TensorSpace w, Scalar w ~ Scalar (IrrepSU2 i j), Scalar w ~ Complex Double) =>
--     LinearFunction (Complex Double) (LinearMap (Complex Double) (IrrepSU2 i j) (IrrepSU2 i j ⊗ w)) w
--   contractTensorMap = undefined -- unsafeCoerce (c1ContractTensorMap @w)
--   contractLinearMapAgainstTensorLookup ::
--     forall w x u.
--     ( TensorSpace w, Scalar w ~ Scalar (IrrepSU2 i j), Scalar w ~ Complex Double
--     , TensorSpace x, Scalar x ~ Scalar (IrrepSU2 i j), Scalar x ~ Complex Double
--     , TensorSpace u, Scalar u ~ Scalar (IrrepSU2 i j), Scalar u ~ Complex Double) =>
--     LinearFunction
--       (Complex Double)
--       (LinearFunction (Complex Double) (LinearFunction (Complex Double) (Tensor (Complex Double) (IrrepSU2 i j) x) x) (LinearFunction (Complex Double) w u))
--       (LinearFunction (Complex Double) (LinearMap (Complex Double) (IrrepSU2 i j) w) u)
--   contractLinearMapAgainstTensorLookup =
--     unsafeCoerce (c1ContractLinearMapAgainstTensorLookup @x @w @u)
--   useTupleLinearSpaceComponents _ = undefined

-- deriving newtype instance KnownNat (SU2IrrepDim i j) => Eq (IrrepSU2 i j)

-- deriving newtype instance KnownNat (SU2IrrepDim i j) => Show (IrrepSU2 i j)

-- deriving newtype instance KnownNat (SU2IrrepDim i j) => Num (IrrepSU2 i j)

-- deriving newtype instance KnownNat (SU2IrrepDim i j) => Fractional (IrrepSU2 i j)

-- deriving newtype instance KnownNat (SU2IrrepDim i j) => Floating (IrrepSU2 i j)

type family N (p :: Z2Irreps) (q :: Z2Irreps) :: Z2Irreps where
  N Odd Even = Odd
  N Even Odd = Odd
  N Even Even = Even
  N Odd Odd = Even


type With (p :: a) = Sing (p :: a)
type (n :: Nat) `X` v = (V n v)


-- instance (DualVector (DualVector v) ~ v, Show (TensorProduct v w))
--       => Show (Tensor s v w) where
--   showsPrec p (Tensor t) =
--     showParen (p > appPrec) $
--       showString "Tensor " . showsPrec (appPrec + 1) t
--    where
--     appPrec = 10

-- instance ((DualVector (DualVector v) ~ v, Scalar v ~ Complex Double, Show (TensorProduct (DualVector v) w))) => Show (LinearMap s v w) where
--   showsPrec p (LinearMap t) =
--     showParen (p > appPrec) $
--       showString "LinearMap " . showsPrec (appPrec + 1) t
--    where
--     appPrec = 10

instance (KnownNat n, AdditiveGroup v) => AdditiveGroup (V n v) where
  zeroV = pure zeroV
  (^+^) = liftA2 (^+^)
  (^-^) = liftA2 (^-^)
  negateV = fmap negateV

instance (KnownNat n, KnownNat m) => AdditiveGroup (M n m) where
  zeroV = konst 0
  (^+^) = (+)
  (^-^) = (-)
  negateV = negate

instance (KnownNat n, KnownNat m) => VectorSpace (M n m) where
  type Scalar (M n m) = Complex Double
  μ *^ v = fromMaybe (error "VectorSpace M n m: create failed")
             . create $ HMat.cmap (* μ) (extract v)

-- Eq (C n) is provided by Numeric.LinearAlgebra.Static.COrphans

unrowC :: (KnownNat n, n ~ Z2IrrepDim p) => M n n -> C n 
unrowC m = fromMaybe (error "unrowC: empty matrix") $ create vec' where 
  vec = G.extract m
  vec' = vec ! 0 

tensor :: forall n m n' m' . (KnownNat n, KnownNat m, KnownNat n', KnownNat m') => (C n -+> C m) -> (C n' -+> C m') -> ((C n ⊗ C n') -+> (C m ⊗ C m'))
tensor f g = LinearFunction \(Tensor (v :: M n' n)) ->
  let
    foo = arr f :: (C n +> C m)
    foo' = (adjoint $ foo) :: (C m +> C n)
    bar = coerce v :: (C n +> C n')
    baz = arr g :: (C n' +> C m')
    comp = baz . bar . foo'
    comp' = getLinearMap comp :: M m' m
  in Tensor comp'


checkZero :: (IrrepU1 (Pos 1) ⊗ IrrepU1 (Pos 3))
checkZero = zeroTensor

-- tensor' :: forall n m n' m' . (KnownNat n, KnownNat m, KnownNat n', KnownNat m')
--   => (IrrepU1 n -+> IrrepU1 m) -> (IrrepU1 n' -+> IrrepU1 m')
--   -> ((IrrepU1 n ⊗ IrrepU1 n') -+> (IrrepU1 m ⊗ IrrepU1 m'))
-- tensor' f g =
--   unsafeCoerce $
--     tensor @1 @1 @1 @1 (unsafeCoerce f :: C 1 -+> C 1) (unsafeCoerce g :: C 1 -+> C 1)
