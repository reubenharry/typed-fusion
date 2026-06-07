{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StandaloneDeriving #-}

module FunctorExperiment where

import Prelude hiding ((.), Functor, fmap)
import Data.Complex (Complex((:+)))
import Data.Kind (Type)
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(Refl))
import Data.VectorSpace (VectorSpace, (*^))
import GHC.TypeLits (Nat, KnownNat, natVal)
import Data.Singletons (sing)
import Control.Category.Constrained (Category(..))
import Control.Functor.Constrained (Functor(fmap))
import Data.AdditiveGroup (AdditiveGroup)
import Math.LinearMap.Category hiding (Functor)
import Math.LinearMap.Asserted (LinearFunction(..))
import Math.VectorSpace.DimensionAware (DimensionAware, Dimensional)
import Numeric.LinearAlgebra.Static (konst)
import qualified Orphans as Lin
import Utils (Z(..))

-- | Type-level U(1) irrep, labelled by charge @n@.
--
-- Each @'U1Irrep n@ is a one-dimensional representation; all intertwiners
-- between distinct charges are trivial (the @ZeroMap@ hom), and intertwiners
-- @'U1Irrep n -> 'U1Irrep n@ are scalars @Complex Double@.
data IrrepU1 = U1Irrep Nat

type family IrrepCharge (r :: IrrepU1) :: Nat where
  IrrepCharge ('U1Irrep n) = n

-- | Witness that every object is a @'U1Irrep n@ for some known @n@.
class IrrepWitness (r :: IrrepU1) where
  irrepRefl :: r :~: 'U1Irrep (IrrepCharge r)

instance KnownNat n => IrrepWitness ('U1Irrep n) where
  irrepRefl = Refl

--------------------------------------------------------------------------------
-- Morphisms between irreps
--------------------------------------------------------------------------------

-- | Intertwiner between one-dimensional U(1) irreps.
--
--   * @'U1Irrep n -> 'U1Irrep n@ — hom space is @Complex Double@ (scalars)
--   * @'U1Irrep n -> 'U1Irrep m@ when @n /= m@ — hom space is ZeroMap
data IntertwinerIrrep (r :: IrrepU1) (q :: IrrepU1) where
  ZeroMap :: IntertwinerIrrep ('U1Irrep n) ('U1Irrep m)
  Scalar :: Complex Double -> IntertwinerIrrep ('U1Irrep n) ('U1Irrep n)

instance Show (IntertwinerIrrep r q) where
  show ZeroMap       = "ZeroMap"
  show (Scalar z)  = show z

--------------------------------------------------------------------------------
-- Category of U(1) irreps
--------------------------------------------------------------------------------

instance Category IntertwinerIrrep where
  type Object IntertwinerIrrep r = IrrepWitness r

  id :: forall a. IrrepWitness a => IntertwinerIrrep a a
  id = case irrepRefl @a of
    Refl -> Scalar 1

  (.) :: forall a b c.
         ( IrrepWitness a, IrrepWitness b, IrrepWitness c )
      => IntertwinerIrrep b c -> IntertwinerIrrep a b -> IntertwinerIrrep a c
  (.) f g = case (irrepRefl @a, irrepRefl @b, irrepRefl @c) of
    (Refl, Refl, Refl) -> compose f g

compose
  :: IntertwinerIrrep ('U1Irrep b) ('U1Irrep c)
  -> IntertwinerIrrep ('U1Irrep a) ('U1Irrep b)
  -> IntertwinerIrrep ('U1Irrep a) ('U1Irrep c)
compose ZeroMap       _         = ZeroMap
compose _           ZeroMap     = ZeroMap
compose (Scalar y) (Scalar x) = Scalar (y * x)

--------------------------------------------------------------------------------
-- Runtime witnesses
--------------------------------------------------------------------------------

data SomeIrrepU1 where
  SomeU1Irrep :: KnownNat n => Proxy n -> SomeIrrepU1

instance Show SomeIrrepU1 where
  show (SomeU1Irrep p) = "U1(" ++ show (natVal p) ++ ")"

class KnownIrrepU1 (r :: IrrepU1) where
  irrepVal :: SomeIrrepU1

instance KnownNat n => KnownIrrepU1 ('U1Irrep n) where
  irrepVal = SomeU1Irrep (Proxy @n)

--------------------------------------------------------------------------------
-- U(1) group action as endomorphisms in the rep category
--------------------------------------------------------------------------------

-- | Phase factor @e^{i n \theta}@ for charge @n@.
u1PhaseFactor :: forall n. KnownNat n => Double -> Complex Double
u1PhaseFactor theta =
  exp ((0 :+ 1) * (theta * fromIntegral (natVal (Proxy @n)) :+ 0))

-- | U(1) acts on each irrep object via endomorphisms @r -> r@ in
-- @IntertwinerIrrep@. Group multiplication is composition; the identity
-- element is @Scalar 1@.
class ActsOnIrrep (r :: IrrepU1) where
  repMorphism :: Double -> IntertwinerIrrep r r

instance KnownNat n => ActsOnIrrep ('U1Irrep n) where
  repMorphism theta = Scalar (u1PhaseFactor @n theta)

-- | Linear representation obtained by applying the representation functor.
repLinear
  :: forall r.
     ( ActsOnIrrep r, IrrepWitness r, KnownNat (IrrepCharge r) )
  => Double
  -> LinearFunction (Complex Double) (RepFunctor r) (RepFunctor r)
repLinear theta = fmap (repMorphism @r theta)

--------------------------------------------------------------------------------
-- Functor to representation spaces
--------------------------------------------------------------------------------

-- | Bridge a type-level charge @n@ to the @Z@ index used by @Lin.IrrepU1@.
type family U1Charge (r :: IrrepU1) :: Lin.U1Irreps where
  U1Charge ('U1Irrep n) = 'Pos n

-- | The representation functor on objects: each @'U1Irrep n@ maps to a
-- one-dimensional complex vector space @Lin.IrrepU1 ('Pos n)@.
newtype RepFunctor (r :: IrrepU1) = RepFunctor (Lin.IrrepU1 (U1Charge r))
  deriving newtype (Eq, Show, Num, Fractional, Floating)

instance KnownNat (IrrepCharge r) => AdditiveGroup (RepFunctor r) where
  RepFunctor v ^+^ RepFunctor w = RepFunctor (v ^+^ w)
  zeroV = RepFunctor zeroV
  negateV (RepFunctor v) = RepFunctor (negateV v)

instance KnownNat (IrrepCharge r) => VectorSpace (RepFunctor r) where
  type Scalar (RepFunctor r) = Complex Double
  μ *^ RepFunctor v = RepFunctor (μ *^ v)

instance KnownNat (IrrepCharge r) => InnerSpace (RepFunctor r) where
  RepFunctor v <.> RepFunctor w = v <.> w

instance KnownNat (IrrepCharge r) => Semimanifold (RepFunctor r) where
  type Needle (RepFunctor r) = Needle (Lin.IrrepU1 (U1Charge r))
  RepFunctor v .+~^ δ = undefined

instance KnownNat (IrrepCharge r) => PseudoAffine (RepFunctor r) where
  RepFunctor v .-~! RepFunctor w = undefined
  RepFunctor v .-~. RepFunctor w = undefined

instance KnownNat (IrrepCharge r) => DimensionAware (RepFunctor r) where
  type StaticDimension (RepFunctor r) = StaticDimension (Lin.IrrepU1 (U1Charge r))
  dimensionalityWitness = undefined

instance (KnownNat (IrrepCharge r), IrrepCharge r ~ n, n ~ 1) => n `Dimensional` RepFunctor r where
  knownDimensionalitySing = sing
  unsafeFromArrayWithOffset i ar =
    RepFunctor (unsafeFromArrayWithOffset i ar)
  unsafeWriteArrayWithOffset ar i (RepFunctor v) =
    unsafeWriteArrayWithOffset ar i v

instance KnownNat (IrrepCharge r) => TensorSpace (RepFunctor r) where
  type TensorProduct (RepFunctor r) w = TensorProduct (Lin.IrrepU1 (U1Charge r)) w
  scalarSpaceWitness = undefined
  linearManifoldWitness = undefined
  zeroTensor = undefined
  toFlatTensor = undefined
  fromFlatTensor = undefined
  addTensors = undefined
  subtractTensors = undefined
  scaleTensor = undefined
  negateTensor = undefined
  tensorProduct = undefined
  transposeTensor = undefined
  fmapTensor = undefined
  fzipTensorWith = undefined
  tensorUnsafeFromArrayWithOffset = undefined
  tensorUnsafeWriteArrayWithOffset = undefined
  coerceFmapTensorProduct = undefined
  wellDefinedVector (RepFunctor v) = RepFunctor <$> wellDefinedVector v
  wellDefinedTensor = undefined
  vectorConjugate = undefined

-- | @IntertwinerIrrep@ is a subcategory of @LinearFunction (Complex Double)@:
--   * @Scalar z@ maps to multiplication by @z@
--   * @ZeroMap@ maps to the zero linear map (the only map into a trivial hom space)
instance Functor RepFunctor IntertwinerIrrep (LinearFunction (Complex Double)) where
  fmap morph = case morph of
    ZeroMap ->
      LinearFunction $ RepFunctor . const (Lin.IrrepU1 (konst 0))
    Scalar z ->
      LinearFunction $ \(RepFunctor v) -> RepFunctor (z *^ v)

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

-- charge 0 -> charge 1: no nonzero intertwiner
zeroToOne :: IntertwinerIrrep ('U1Irrep 0) ('U1Irrep 1)
zeroToOne = ZeroMap

-- charge 1 -> charge 1: multiplication by i
phase :: IntertwinerIrrep ('U1Irrep 1) ('U1Irrep 1)
phase = Scalar (0 :+ 1)

-- rotation by π/2 on charge +1 is the same endomorphism as @phase@
phaseFromAction :: IntertwinerIrrep ('U1Irrep 1) ('U1Irrep 1)
phaseFromAction = repMorphism @('U1Irrep 1) (pi / 2)

-- composition of group elements is composition of intertwiners
composedAction :: IntertwinerIrrep ('U1Irrep 1) ('U1Irrep 1)
composedAction = repMorphism @('U1Irrep 1) 1 . repMorphism @('U1Irrep 1) 2

-- composition: phase . phase = Scalar (-1)
phaseSquared :: IntertwinerIrrep ('U1Irrep 1) ('U1Irrep 1)
phaseSquared = phase . phase

-- charge-1 representation space, and the linear map corresponding to @phase@
repSpace1 :: RepFunctor ('U1Irrep 1)
repSpace1 = RepFunctor (Lin.IrrepU1 (konst 1))

phaseLinear
  :: LinearFunction (Complex Double)
       (RepFunctor ('U1Irrep 1))
       (RepFunctor ('U1Irrep 1))
phaseLinear = fmap phase

-- linear action by π/2 matches @phaseLinear@
phaseLinearFromAction
  :: LinearFunction (Complex Double)
       (RepFunctor ('U1Irrep 1))
       (RepFunctor ('U1Irrep 1))
phaseLinearFromAction = repLinear @('U1Irrep 1) (pi / 2)
