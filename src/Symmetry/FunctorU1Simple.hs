{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Scalar U(1) irrep categories — self-contained (no other @Symmetry.*@ imports).
--
-- Objects are @'Rep p@ for a charge @p :: Z@. Morphisms are intertwiners only:
-- a scalar @Complex Double@ when @p = q@ (Schur), and @()@ when @p ≠ q@.
--
-- The forgetful functor @'ForgetTag'@ maps @'Rep p'@ to @C 1@ and morphisms to
-- @'LinearFunction'@s. Canonical fusion of tensor products lives in the
-- forgetful/monoidal layer (@TensorNetwork.Categorical@), not in this category.
module Symmetry.FunctorU1Simple
  ( -- * Charges and irreps
    Z (..)
  , ZEq
  , U1Rep (..)
  , U1IrrepDim
    -- * Intertwiner indexing
  , FullMapIndex
  , ZIsZero
  , IntertwinerOk
    -- * Forgetful functor
  , Forget
  , ForgetTag (..)
    -- * Intertwiner category
  , InterHom
  , U1Mor (..)
  , scalarMor
  , crossMor
  , phase
  , phaseSquared
  , demoPhase
  , posToNeg
  , negToPos
  , posRoundTrip
  , demoZeroCross
  , demoRoundTrip
  ) where

import Prelude hiding ((.), id, Functor (..))
import Control.Category.Constrained (Category (..))
import Control.Functor.Constrained (Functor (..))
import Data.Complex (Complex ((:+)))
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))
import Data.Singletons (sing)
import Data.Type.Ord (OrderingI (EQI, LTI, GTI))
import GHC.TypeLits (KnownNat, Nat, CmpNat, type (+), type (-))
import qualified GHC.TypeNats
import Unsafe.Coerce (unsafeCoerce)
import Math.LinearMap.Asserted (getLinearFunction, linearFunction)
import Math.LinearMap.Category
  ( LinearFunction (..), TensorSpace (..), AdditiveGroup (..), VectorSpace (..)
  , InnerSpace (..), DimensionAware (..), Semimanifold (..), PseudoAffine (..) )
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.VectorSpace.DimensionAware
  (Dimensional (..), unsafeFromArrayWithOffset, unsafeWriteArrayWithOffset)
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, Sized (konst))

--------------------------------------------------------------------------------
-- Charges
--------------------------------------------------------------------------------

data Z = Neg Nat | Zero | Pos Nat

type family Negate (z :: Z) :: Z where
  Negate 'Zero   = 'Zero
  Negate ('Pos n) = 'Neg n
  Negate ('Neg n) = 'Pos n

type family Add (a :: Z) (b :: Z) :: Z where
  Add 'Zero b = b
  Add a 'Zero = a
  Add ('Pos a) ('Pos b) = 'Pos (a + b)
  Add ('Neg a) ('Neg b) = 'Neg (a + b)
  Add ('Pos a) ('Neg b) = AddPosNeg (CmpNat a b) a b
  Add ('Neg a) ('Pos b) = AddPosNeg (CmpNat b a) b a

type family AddPosNeg (o :: Ordering) (a :: Nat) (b :: Nat) :: Z where
  AddPosNeg 'EQ a b = 'Zero
  AddPosNeg 'LT a b = 'Neg (b - a)
  AddPosNeg 'GT a b = 'Pos (a - b)

type family OrdEq (o :: Ordering) :: Bool where
  OrdEq 'EQ = 'True
  OrdEq 'LT = 'False
  OrdEq 'GT = 'False

type family NatEq (a :: Nat) (b :: Nat) :: Bool where
  NatEq a b = OrdEq (CmpNat a b)

type family ZEq (a :: Z) (b :: Z) :: Bool where
  ZEq 'Zero 'Zero = 'True
  ZEq ('Pos a) ('Pos b) = NatEq a b
  ZEq ('Neg a) ('Neg b) = NatEq a b
  ZEq _ _ = 'False

--------------------------------------------------------------------------------
-- Objects of the U(1) rep category
--------------------------------------------------------------------------------

-- | Object of the U(1) rep category: a single charge label.
data U1Rep where
  Rep :: Z -> U1Rep

type family U1IrrepDim (r :: U1Rep) :: Nat where
  U1IrrepDim ('Rep _) = 1

--------------------------------------------------------------------------------
-- Forgetful functor image
--------------------------------------------------------------------------------

type family Forget (r :: U1Rep) :: Type where
  Forget ('Rep p) = C (U1IrrepDim ('Rep p))

newtype ForgetTag (r :: U1Rep) = ForgetTag { unForgetTag :: Forget r }

instance KnownNat (U1IrrepDim ('Rep p)) => AdditiveGroup (ForgetTag ('Rep p)) where
  ForgetTag a ^+^ ForgetTag b = ForgetTag (a ^+^ b)
  zeroV = ForgetTag zeroV
  negateV (ForgetTag v) = ForgetTag (negateV v)

instance KnownNat (U1IrrepDim ('Rep p)) => VectorSpace (ForgetTag ('Rep p)) where
  type Scalar (ForgetTag ('Rep p)) = Complex Double
  μ *^ ForgetTag v = ForgetTag (μ *^ v)

instance KnownNat (U1IrrepDim ('Rep p)) => InnerSpace (ForgetTag ('Rep p)) where
  ForgetTag v <.> ForgetTag w = v <.> w

instance KnownNat (U1IrrepDim ('Rep p)) => DimensionAware (ForgetTag ('Rep p)) where
  type StaticDimension (ForgetTag ('Rep p)) = StaticDimension (C (U1IrrepDim ('Rep p)))
  dimensionalityWitness = undefined

instance (KnownNat (U1IrrepDim ('Rep p)), n ~ U1IrrepDim ('Rep p))
  => n `Dimensional` ForgetTag ('Rep p) where
  knownDimensionalitySing = sing
  unsafeFromArrayWithOffset i ar =
    ForgetTag (unsafeFromArrayWithOffset i ar)
  unsafeWriteArrayWithOffset ar i (ForgetTag v) =
    unsafeWriteArrayWithOffset ar i v

instance KnownNat (U1IrrepDim ('Rep p)) => Semimanifold (ForgetTag ('Rep p)) where
  type Needle (ForgetTag ('Rep p)) = C (U1IrrepDim ('Rep p))
  ForgetTag _ .+~^ _ = undefined

instance KnownNat (U1IrrepDim ('Rep p)) => PseudoAffine (ForgetTag ('Rep p)) where
  ForgetTag _ .-~! ForgetTag _ = undefined
  ForgetTag _ .-~. ForgetTag _ = undefined

instance KnownNat (U1IrrepDim ('Rep p)) => TensorSpace (ForgetTag ('Rep p)) where
  type TensorProduct (ForgetTag ('Rep p)) w = TensorProduct (C (U1IrrepDim ('Rep p))) w
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
  wellDefinedVector (ForgetTag v) = ForgetTag <$> wellDefinedVector v
  wellDefinedTensor = undefined
  vectorConjugate = undefined

--------------------------------------------------------------------------------
-- Intertwiner indexing
--------------------------------------------------------------------------------

type FullMapIndex (r :: Z) (s :: Z) = Add s (Negate r)

type family ZIsZero (z :: Z) :: Bool where
  ZIsZero 'Zero = 'True
  ZIsZero _     = 'False

type family IntertwinerOk (r :: Z) (s :: Z) :: Bool where
  IntertwinerOk r s = ZIsZero (FullMapIndex r s)

type family InterHom (r :: Z) (s :: Z) :: Type where
  InterHom r s = HomIf (ZEq r s)

type family HomIf (eq :: Bool) :: Type where
  HomIf 'True  = Complex Double
  HomIf 'False = ()

--------------------------------------------------------------------------------
-- Charge witnesses (for compose / apply)
--------------------------------------------------------------------------------

data SingZ (z :: Z) where
  SZero :: SingZ 'Zero
  SPos  :: KnownNat n => SingZ ('Pos n)
  SNeg  :: KnownNat n => SingZ ('Neg n)

class KnownSingZ (z :: Z) where
  singZ :: SingZ z

instance KnownSingZ 'Zero where singZ = SZero
instance KnownNat n => KnownSingZ ('Pos n) where singZ = SPos @n
instance KnownNat n => KnownSingZ ('Neg n) where singZ = SNeg @n

data ZCmp (a :: Z) (b :: Z) where
  ZSame :: ZEq a b ~ 'True => ZCmp a b
  ZDiff :: ZEq a b ~ 'False => ZCmp a b

zDiff :: forall a b. ZEq a b ~ 'False => ZCmp a b
zDiff = ZDiff

zCmp :: SingZ a -> SingZ b -> ZCmp a b
zCmp SZero SZero = ZSame
zCmp SZero (SPos @n) = zDiff @'Zero @('Pos n)
zCmp SZero (SNeg @n) = zDiff @'Zero @('Neg n)
zCmp (SPos @n) SZero = zDiff @('Pos n) @'Zero
zCmp (SNeg @n) SZero = zDiff @('Neg n) @'Zero
zCmp (SPos @a) (SPos @b) =
  case GHC.TypeNats.cmpNat (Proxy @a) (Proxy @b) of
    EQI -> ZSame
    LTI -> zDiff @('Pos a) @('Pos b)
    GTI -> zDiff @('Pos a) @('Pos b)
zCmp (SNeg @a) (SNeg @b) =
  case GHC.TypeNats.cmpNat (Proxy @a) (Proxy @b) of
    EQI -> ZSame
    LTI -> zDiff @('Neg a) @('Neg b)
    GTI -> zDiff @('Neg a) @('Neg b)
zCmp (SPos @a) (SNeg @b) = zDiff @('Pos a) @('Neg b)
zCmp (SNeg @a) (SPos @b) = zDiff @('Neg a) @('Pos b)

composeHom
  :: forall a b c.
     (KnownSingZ a, KnownSingZ b, KnownSingZ c)
  => InterHom a b -> InterHom b c -> InterHom a c
composeHom ab bc = composeHomSing (singZ @a) (singZ @b) (singZ @c) ab bc

composeHomSing
  :: SingZ a -> SingZ b -> SingZ c
  -> InterHom a b -> InterHom b c -> InterHom a c
composeHomSing sa sb sc ab bc =
  case (zCmp sa sb, zCmp sb sc, zCmp sa sc) of
    (ZSame, ZSame, ZSame) ->
      (bc :: Complex Double) * (ab :: Complex Double)
    (_, _, ZSame) -> 0
    (_, _, ZDiff) -> unsafeCoerce ()

applyHomLinear
  :: SingZ p -> SingZ q -> InterHom p q -> C (U1IrrepDim ('Rep p)) -> C (U1IrrepDim ('Rep q))
applyHomLinear sp sq hom v =
  case zCmp sp sq of
    ZSame -> hom *^ v
    ZDiff -> konst 0

applyHomLinearZ
  :: forall p q. (KnownSingZ p, KnownSingZ q)
  => InterHom p q -> C (U1IrrepDim ('Rep p)) -> C (U1IrrepDim ('Rep q))
applyHomLinearZ hom v = applyHomLinear (singZ @p) (singZ @q) hom v

type family RepZ (r :: U1Rep) :: Z where
  RepZ ('Rep p) = p

type Pos1 = 'Pos 1
type Neg1 = 'Neg 1
type RepPos1 = 'Rep Pos1
type RepNeg1 = 'Rep Neg1

--------------------------------------------------------------------------------
-- Category of intertwiners
--------------------------------------------------------------------------------

data U1Mor (a :: U1Rep) (b :: U1Rep) where
  RepMor :: forall p q. InterHom p q -> U1Mor ('Rep p) ('Rep q)

scalarMor :: forall p. (ZEq p p ~ 'True) => Complex Double -> U1Mor ('Rep p) ('Rep p)
scalarMor z = RepMor z

crossMor :: forall p q. (ZEq p q ~ 'False) => U1Mor ('Rep p) ('Rep q)
crossMor = RepMor (() :: InterHom p q)

composeU1Mor
  :: forall a b c.
     (Object U1Mor a, Object U1Mor b, Object U1Mor c)
  => U1Mor b c -> U1Mor a b -> U1Mor a c
composeU1Mor (RepMor bc) (RepMor ab) =
  RepMor (composeHom @(RepZ a) @(RepZ b) @(RepZ c) ab bc)

type family ObjectU1Mor (a :: U1Rep) :: Constraint where
  ObjectU1Mor ('Rep p) =
    ( KnownNat (U1IrrepDim ('Rep p)), KnownSingZ p, ZEq p p ~ 'True )

type family ObjReflexive (a :: U1Rep) :: Constraint where
  ObjReflexive ('Rep p) = ('Rep p ~ 'Rep (RepZ ('Rep p)))

instance Category U1Mor where
  type Object U1Mor a = (ObjectU1Mor a, ObjReflexive a)
  id = unsafeCoerce (scalarMor 1 :: U1Mor RepPos1 RepPos1)
  (.) = composeU1Mor

repMorLinear
  :: forall p q.
     ( KnownSingZ p, KnownSingZ q
     , KnownNat (U1IrrepDim ('Rep p)), KnownNat (U1IrrepDim ('Rep q))
     )
  => InterHom p q
  -> LinearFunction (Complex Double) (ForgetTag ('Rep p)) (ForgetTag ('Rep q))
repMorLinear hom =
  linearFunction $ \(ForgetTag v) ->
    ForgetTag (applyHomLinearZ @p @q hom v)

instance Functor ForgetTag U1Mor (LinearFunction (Complex Double)) where
  fmap (RepMor mor) = repMorLinear mor

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

phase :: U1Mor RepPos1 RepPos1
phase = scalarMor (0 :+ 1)

phaseSquared :: U1Mor RepPos1 RepPos1
phaseSquared = phase . phase

demoPhase :: C 1 -> C 1
demoPhase v =
  unForgetTag (getLinearFunction (fmap phase) (ForgetTag @RepPos1 v))

posToNeg :: U1Mor RepPos1 RepNeg1
posToNeg = crossMor

negToPos :: U1Mor RepNeg1 RepPos1
negToPos = crossMor

-- | @+1 → -1 → +1@ composes to scalar @0@, not @id@.
posRoundTrip :: U1Mor RepPos1 RepPos1
posRoundTrip = negToPos . posToNeg

demoZeroCross :: C 1 -> C 1
demoZeroCross v =
  unForgetTag (getLinearFunction (fmap posToNeg) (ForgetTag @RepPos1 v))

demoRoundTrip :: C 1 -> C 1
demoRoundTrip v =
  unForgetTag (getLinearFunction (fmap posRoundTrip) (ForgetTag @RepPos1 v))

-- | Type-level sanity checks.
posToNegInter :: (InterHom Pos1 Neg1 ~ (), IntertwinerOk Pos1 Neg1 ~ 'False) => ()
posToNegInter = ()

posRoundTripInter :: (InterHom Pos1 Pos1 ~ Complex Double) => ()
posRoundTripInter = ()
