{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}

module FunctorExperiment where

import Prelude hiding ((.), Functor, fmap)
import Data.Complex (Complex((:+)))
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(Refl))
import GHC.TypeLits (Nat)
import Data.Singletons (sing)
import Control.Category.Constrained (Category(..))
import Control.Functor.Constrained (Functor(fmap))
import Math.LinearMap.Category hiding (Tensor)
import Math.LinearMap.Category.Instances.Deriving ()
import Numeric.LinearAlgebra.Static (konst)
import Unsafe.Coerce (unsafeCoerce)
import General (DualRep, Tensor, FilterNonTrivial, Group(U1))
import qualified Orphans as Lin
import Utils (Z(..), KnownZ, getZ, zVal)

-- | Type-level U(1) irrep, labelled by charge @z@.
--
-- Each @'U1Irrep z@ is one-dimensional. Intertwiners @r -> q@ are indexed
-- by @HomSectorList r q@: either empty (@InterNil@) or scalar (@InterScalar@).
data IrrepU1 = U1Irrep Z

-- | Witness that every object is a @'U1Irrep z@ for some known @z@.
class KnownZ (ObjCharge r) => IrrepObj (r :: IrrepU1) where
  type ObjCharge r :: Z
  objRefl :: r :~: 'U1Irrep (ObjCharge r)

instance KnownZ z => IrrepObj ('U1Irrep z) where
  type ObjCharge ('U1Irrep z) = z
  objRefl = Refl

-- | Embed a single irrep object as a one-sector rep list.
type family AsList (r :: IrrepU1) :: [(Z, Nat)] where
  AsList ('U1Irrep z) = '[ '(z, 1)]

-- | Hom-space sector list for intertwiners @r -> q@.
--
-- @FilterNonTrivial U1 (Tensor U1 (DualRep U1 (AsList r)) (AsList q))@.
-- The endo clause avoids GHC getting stuck on @Add (Negate z) z@.
type family HomSectorList (r :: IrrepU1) (q :: IrrepU1) :: [(Z, Nat)] where
  HomSectorList ('U1Irrep z) ('U1Irrep z) = '[ '(Zero, 1)]
  HomSectorList ('U1Irrep z) ('U1Irrep w) =
    FilterNonTrivial U1
      (Tensor U1
        (DualRep U1 (AsList ('U1Irrep z)))
        (AsList ('U1Irrep w)))

-- | An intertwiner is determined by its hom-sector list.
--
-- Future: @InterBlock@ for @'[ '(Zero, m) ]@ with @m > 1@, @InterCons@ for
-- multiple sectors.
data IntertwinerSectors (hom :: [(Z, Nat)]) (r :: IrrepU1) (q :: IrrepU1) where
  InterNil    :: IntertwinerSectors '[] r q
  InterScalar :: Complex Double -> IntertwinerSectors '[ '(Zero, 1)] r r

instance Show (IntertwinerSectors hom r q) where
  show InterNil        = "InterNil"
  show (InterScalar z) = show z

newtype Intertwiner (r :: IrrepU1) (q :: IrrepU1) = MkIntertwiner
  { unIntertwiner :: IntertwinerSectors (HomSectorList r q) r q
  }
  deriving Show via (IntertwinerSectors (HomSectorList r q) r q)

-- | Compose after exposing @'U1Irrep z@ heads so @HomSectorList@ reduces.
--
-- When a factor is @InterNil@ but the composed hom is endomorphic, the zero
-- map is @InterScalar 0@; GHC cannot prove this from @HomSectorList@ alone.
composeVia
  :: forall za zb zc a' b' c'.
     (KnownZ za, KnownZ zb, KnownZ zc)
  => a' :~: 'U1Irrep za
  -> b' :~: 'U1Irrep zb
  -> c' :~: 'U1Irrep zc
  -> IntertwinerSectors (HomSectorList a' b') a' b'
  -> IntertwinerSectors (HomSectorList b' c') b' c'
  -> IntertwinerSectors (HomSectorList a' c') a' c'
composeVia Refl Refl Refl ab bc = case (ab, bc) of
  (InterScalar x, InterScalar y) -> unsafeCoerce (InterScalar (y * x))
  _ | zVal (Proxy @za) == zVal (Proxy @zc) -> unsafeCoerce (InterScalar 0)
    | otherwise -> unsafeCoerce InterNil

compose
  :: forall a b c.
     (IrrepObj a, IrrepObj b, IrrepObj c)
  => Intertwiner b c
  -> Intertwiner a b
  -> Intertwiner a c
compose (MkIntertwiner bc) (MkIntertwiner ab) =
  MkIntertwiner (composeVia (objRefl @a) (objRefl @b) (objRefl @c) ab bc)

instance Category Intertwiner where
  type Object Intertwiner r = IrrepObj r

  id :: forall a. IrrepObj a => Intertwiner a a
  id = MkIntertwiner (endoScalar (objRefl @a))
    where
      endoScalar
        :: r :~: 'U1Irrep z
        -> IntertwinerSectors (HomSectorList r r) r r
      endoScalar Refl = InterScalar 1

  (.) = compose

-- | Phase factor @e^{i q \theta}@ for charge @q@.
u1PhaseFactor :: forall z. KnownZ z => Double -> Complex Double
u1PhaseFactor theta =
  exp ((0 :+ 1) * (fromIntegral (getZ @z) * theta :+ 0))

-- | U(1) group action on representation spaces (not intertwiner morphisms).
class IrrepObj r => ActsOnIrrep (r :: IrrepU1) where
  repLinear :: Double -> LinearFunction (Complex Double) (RepFunctor r) (RepFunctor r)

instance KnownZ z => ActsOnIrrep ('U1Irrep z) where
  repLinear theta =
    LinearFunction $ \(RepFunctor v) -> RepFunctor (u1PhaseFactor @z theta *^ v)

newtype RepFunctor (r :: IrrepU1) = RepFunctor (Lin.IrrepU1 (ObjCharge r))
  deriving newtype (Eq, Show, Num, Fractional, Floating)

instance IrrepObj r => AdditiveGroup (RepFunctor r) where
  RepFunctor v ^+^ RepFunctor w = RepFunctor (v ^+^ w)
  zeroV = RepFunctor zeroV
  negateV (RepFunctor v) = RepFunctor (negateV v)

instance IrrepObj r => VectorSpace (RepFunctor r) where
  type Scalar (RepFunctor r) = Complex Double
  μ *^ RepFunctor v = RepFunctor (μ *^ v)

instance IrrepObj r => InnerSpace (RepFunctor r) where
  RepFunctor v <.> RepFunctor w = v <.> w

-- Minimal @TensorSpace@ stubs so @RepFunctor@ is a valid @Functor@ codomain.
instance IrrepObj r => Semimanifold (RepFunctor r) where
  type Needle (RepFunctor r) = Needle (Lin.IrrepU1 (ObjCharge r))
  RepFunctor _ .+~^ _ = undefined

instance IrrepObj r => PseudoAffine (RepFunctor r) where
  RepFunctor _ .-~! RepFunctor _ = undefined
  RepFunctor _ .-~. RepFunctor _ = undefined

instance IrrepObj r => DimensionAware (RepFunctor r) where
  type StaticDimension (RepFunctor r) = StaticDimension (Lin.IrrepU1 (ObjCharge r))
  dimensionalityWitness = undefined

instance IrrepObj r => 1 `Dimensional` RepFunctor r where
  knownDimensionalitySing = sing
  unsafeFromArrayWithOffset i ar =
    RepFunctor (unsafeFromArrayWithOffset i ar)
  unsafeWriteArrayWithOffset ar i (RepFunctor v) =
    unsafeWriteArrayWithOffset ar i v

instance IrrepObj r => TensorSpace (RepFunctor r) where
  type TensorProduct (RepFunctor r) w = TensorProduct (Lin.IrrepU1 (ObjCharge r)) w
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

intertwinerLinear
  :: forall a b.
     (IrrepObj a, IrrepObj b)
  => Intertwiner a b
  -> LinearFunction (Complex Double) (RepFunctor a) (RepFunctor b)
intertwinerLinear (MkIntertwiner sectors) = LinearFunction $ \case
  RepFunctor v -> case sectors of
    InterNil      -> RepFunctor (Lin.IrrepU1 (konst 0))
    InterScalar z -> RepFunctor (z *^ v)

instance Functor RepFunctor Intertwiner (LinearFunction (Complex Double)) where
  fmap = intertwinerLinear

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

type ZeroToOneHom = HomSectorList ('U1Irrep 'Zero) ('U1Irrep ('Pos 1))
type PhaseHom     = HomSectorList ('U1Irrep ('Pos 1)) ('U1Irrep ('Pos 1))
type NegPosHom    = HomSectorList ('U1Irrep ('Neg 1)) ('U1Irrep ('Pos 1))

zeroToOneEmpty :: (ZeroToOneHom ~ '[]) => ()
zeroToOneEmpty = ()

phaseHom :: (PhaseHom ~ '[ '(Zero, 1)]) => ()
phaseHom = ()

negPosHom :: (NegPosHom ~ '[]) => ()
negPosHom = ()

zeroToOne :: Intertwiner ('U1Irrep 'Zero) ('U1Irrep ('Pos 1))
zeroToOne = MkIntertwiner InterNil

phase :: Intertwiner ('U1Irrep ('Pos 1)) ('U1Irrep ('Pos 1))
phase = MkIntertwiner (InterScalar (0 :+ 1))

phaseSquared :: Intertwiner ('U1Irrep ('Pos 1)) ('U1Irrep ('Pos 1))
phaseSquared = phase . phase

repSpace1 :: RepFunctor ('U1Irrep ('Pos 1))
repSpace1 = RepFunctor (Lin.IrrepU1 (konst 1))

phaseLinear :: LinearFunction (Complex Double)
  (RepFunctor ('U1Irrep ('Pos 1))) (RepFunctor ('U1Irrep ('Pos 1)))
phaseLinear = fmap phase

phaseLinearFromAction :: LinearFunction (Complex Double)
  (RepFunctor ('U1Irrep ('Pos 1))) (RepFunctor ('U1Irrep ('Pos 1)))
phaseLinearFromAction = repLinear @('U1Irrep ('Pos 1)) (pi / 2)

composedLinearAction :: LinearFunction (Complex Double)
  (RepFunctor ('U1Irrep ('Pos 1))) (RepFunctor ('U1Irrep ('Pos 1)))
composedLinearAction =
  repLinear @('U1Irrep ('Pos 1)) 1 . repLinear @('U1Irrep ('Pos 1)) 2

repSpaceNeg1 :: RepFunctor ('U1Irrep ('Neg 1))
repSpaceNeg1 = RepFunctor (Lin.IrrepU1 (konst 1))

negChargeAction :: LinearFunction (Complex Double)
  (RepFunctor ('U1Irrep ('Neg 1))) (RepFunctor ('U1Irrep ('Neg 1)))
negChargeAction = repLinear @('U1Irrep ('Neg 1)) (pi / 2)
