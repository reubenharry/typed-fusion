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
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Scalar U(1) irrep categories — self-contained (no other @Symmetry.*@ imports).
--
-- Each irrep is a one-dimensional complex vector tagged by charge @p :: Z@.
--
-- * @U1Map@ — all linear maps @r → s@; hom object at charge @s - r@.
-- * @U1Mor@ — intertwiners only: hom is a scalar @Complex Double@ when
--   @r = s@ (Schur), and @()@ when @r ≠ s@ (the unique zero map).
module Symmetry.FunctorU1Simple
  ( -- * Charges and irreps
    Z (..)
  , ZEq
  , U1Irreps
  , IrrepU1 (..)
  , U1IrrepDim
    -- * Full-map category
  , U1Map (..)
  , FullMapHom
  , FullMapIndex
  , ZIsZero
  , IntertwinerOk
  , scalarMap
  , applyU1Map
  , demoMapRoundTrip
    -- * Intertwiner category
  , InterHom
  , U1Mor (..)
  , scalarMor
  , crossMor
  , applyMor
  , phase
  , phaseSquared
  , demoPhase
  , posToNeg
  , negToPos
  , posRoundTrip
  , demoZeroCross
  , demoRoundTrip
  ) where

import Prelude hiding ((.), id)
import Control.Category.Constrained (Category (..))
import Data.Complex (Complex ((:+)))
import Data.Kind (Type)
import Data.AdditiveGroup (AdditiveGroup (..))
import Data.Proxy (Proxy (..))
import Data.Type.Ord (OrderingI (EQI, LTI, GTI))
import Data.VectorSpace (VectorSpace (..), (*^))
import GHC.TypeLits (KnownNat, Nat, CmpNat, type (+), type (-))
import qualified GHC.TypeNats
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
-- Scalar irreps
--------------------------------------------------------------------------------

type U1Irreps = Z

type family U1IrrepDim (p :: U1Irreps) :: Nat where
  U1IrrepDim _ = 1

newtype IrrepU1 (p :: U1Irreps) = IrrepU1 { unIrrepU1 :: C (U1IrrepDim p) }

deriving newtype instance KnownNat (U1IrrepDim p) => AdditiveGroup (IrrepU1 p)

instance KnownNat (U1IrrepDim p) => VectorSpace (IrrepU1 p) where
  type Scalar (IrrepU1 p) = Complex Double
  μ *^ IrrepU1 v = IrrepU1 (μ *^ v)

--------------------------------------------------------------------------------
-- Full-map hom indexing (U1Map)
--------------------------------------------------------------------------------

type FullMapIndex (r :: Z) (s :: Z) = Add s (Negate r)

type FullMapHom (r :: Z) (s :: Z) = IrrepU1 (FullMapIndex r s)

type family ZIsZero (z :: Z) :: Bool where
  ZIsZero 'Zero = 'True
  ZIsZero _     = 'False

type family IntertwinerOk (r :: Z) (s :: Z) :: Bool where
  IntertwinerOk r s = ZIsZero (FullMapIndex r s)

--------------------------------------------------------------------------------
-- Intertwiner hom: scalar iff charges match, else uninhabited carrier @()@
--------------------------------------------------------------------------------

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
composeHom ab bc =
  case ( zCmp (singZ @a) (singZ @b)
       , zCmp (singZ @b) (singZ @c)
       , zCmp (singZ @a) (singZ @c)
       ) of
    (ZSame, ZSame, ZSame) ->
      (bc :: Complex Double) * (ab :: Complex Double)
    (_, _, ZSame) -> 0
    (_, _, ZDiff) -> (() :: InterHom a c)

applyHom
  :: forall p q. (KnownSingZ p, KnownSingZ q)
  => InterHom p q -> IrrepU1 p -> IrrepU1 q
applyHom hom (IrrepU1 v) =
  case zCmp (singZ @p) (singZ @q) of
    ZSame -> IrrepU1 (hom *^ v)
    ZDiff -> IrrepU1 (konst 0)

--------------------------------------------------------------------------------
-- Category of all linear maps
--------------------------------------------------------------------------------

newtype U1Map (r :: U1Irreps) (s :: U1Irreps) = MkU1Map
  { unU1Map :: FullMapHom r s }

scalarMap :: Complex Double -> U1Map r s
scalarMap z = MkU1Map (IrrepU1 (konst z))

composeMap
  :: forall a b c. KnownNat (U1IrrepDim (FullMapIndex a c))
  => U1Map b c -> U1Map a b -> U1Map a c
composeMap (MkU1Map (IrrepU1 bc)) (MkU1Map (IrrepU1 ab)) =
  MkU1Map (IrrepU1 (bc * ab))

instance Category U1Map where
  type Object U1Map p = KnownNat (U1IrrepDim p)
  id = scalarMap 1
  (.) = composeMap

applyMap :: FullMapHom r s -> IrrepU1 r -> IrrepU1 s
applyMap (IrrepU1 m) (IrrepU1 v) = IrrepU1 (m * v)

applyU1Map :: U1Map r s -> IrrepU1 r -> IrrepU1 s
applyU1Map (MkU1Map hom) = applyMap hom

--------------------------------------------------------------------------------
-- Category of intertwiners
--------------------------------------------------------------------------------

newtype U1Mor (p :: U1Irreps) (q :: U1Irreps) = MkU1Mor
  { unU1Mor :: InterHom p q }

scalarMor :: forall p. (ZEq p p ~ 'True) => Complex Double -> U1Mor p p
scalarMor z = MkU1Mor z

crossMor :: forall p q. (ZEq p q ~ 'False) => U1Mor p q
crossMor = MkU1Mor (() :: InterHom p q)

composeMor
  :: forall a b c.
     (KnownSingZ a, KnownSingZ b, KnownSingZ c)
  => U1Mor b c -> U1Mor a b -> U1Mor a c
composeMor (MkU1Mor bc) (MkU1Mor ab) =
  MkU1Mor (composeHom @a @b @c ab bc)

instance Category U1Mor where
  type Object U1Mor p = (KnownNat (U1IrrepDim p), KnownSingZ p, ZEq p p ~ 'True)
  id = scalarMor 1
  (.) = composeMor

applyMor :: (KnownSingZ p, KnownSingZ q) => U1Mor p q -> IrrepU1 p -> IrrepU1 q
applyMor (MkU1Mor hom) = applyHom hom

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

type Pos1 = 'Pos 1
type Neg1 = 'Neg 1

phase :: U1Mor Pos1 Pos1
phase = scalarMor (0 :+ 1)

phaseSquared :: U1Mor Pos1 Pos1
phaseSquared = phase . phase

demoPhase :: C 1 -> C 1
demoPhase v = unIrrepU1 (applyMor phase (IrrepU1 v))

posToNeg :: U1Mor Pos1 Neg1
posToNeg = crossMor

negToPos :: U1Mor Neg1 Pos1
negToPos = crossMor

-- | @+1 → -1 → +1@ composes to scalar @0@, not @id@.
posRoundTrip :: U1Mor Pos1 Pos1
posRoundTrip = negToPos . posToNeg

demoZeroCross :: C 1 -> C 1
demoZeroCross v = unIrrepU1 (applyMor posToNeg (IrrepU1 v))

demoRoundTrip :: C 1 -> C 1
demoRoundTrip v = unIrrepU1 (applyMor posRoundTrip (IrrepU1 v))

posToNegMap :: U1Map Pos1 Neg1
posToNegMap = scalarMap 1

negToPosMap :: U1Map Neg1 Pos1
negToPosMap = scalarMap 1

posRoundTripMap :: U1Map Pos1 Pos1
posRoundTripMap = negToPosMap . posToNegMap

demoMapRoundTrip :: C 1 -> C 1
demoMapRoundTrip v = unIrrepU1 (applyU1Map posRoundTripMap (IrrepU1 v))

-- | Type-level sanity checks.
posToNegInter :: (InterHom Pos1 Neg1 ~ (), IntertwinerOk Pos1 Neg1 ~ 'False) => ()
posToNegInter = ()

posRoundTripInter :: (InterHom Pos1 Pos1 ~ Complex Double) => ()
posRoundTripInter = ()
