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
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE IncoherentInstances #-}

module FunctorExperiment where

import Data.Vector.Storable ((!))

import Prelude hiding ((.), Functor, fmap)
import Data.Complex (Complex((:+)))
import GHC.TypeLits (Nat, KnownNat, type (+), type (*))
import Data.Singletons (sing)
import Control.Category.Constrained (Category(..))
import Control.Functor.Constrained (Functor(fmap))
import Math.LinearMap.Category hiding (Tensor)
import Math.LinearMap.Category.Instances.Deriving ()
import Numeric.LinearAlgebra.Static (C, M, konst, extract, Sized(fromList), Domain(app))
import Data.Vector.Storable (toList)
import Unsafe.Coerce (unsafeCoerce)
import General (DualRep, Tensor, FilterNonTrivial, Group(U1))
import Utils (Z(..), KnownZ, getZ)

-- | A U(1) representation as a list of @(charge, multiplicity)@ sectors.
type U1Rep = [(Z, Nat)]

-- | Single-charge irrep @q@ (multiplicity @1@).

-- | Total dimension of a U(1) rep (sum of sector multiplicities).
type family RepDim (r :: U1Rep) :: Nat where
  RepDim '[] = 0
  RepDim ('(z, m) ': rs) = m + RepDim rs

-- | Hom dimension for endomorphisms of a single @m@-fold sector (@m × m@).
type family EndoHomDim (m :: Nat) :: Nat where
  EndoHomDim m = m * m

-- | Every sector in the list has a known charge and multiplicity.
class U1RepList (rs :: U1Rep)

instance U1RepList '[]
instance
  ( KnownNat m, KnownZ z, U1RepList rest
  ) => U1RepList ('(z, m) ': rest)

-- | Hom-space sector list for intertwiners @r -> q@.
type family HomSectorList (r :: U1Rep) (q :: U1Rep) :: [(Z, Nat)] where
  HomSectorList '[ '(z, 1)] '[ '(z, 1)] = '[ '(Zero, 1)]
  HomSectorList r q =
    FilterNonTrivial U1 (Tensor U1 (DualRep U1 r) q)

-- | Intertwiner data indexed by its hom-sector spine.
data IntertwinerSectors (hom :: [(Z, Nat)]) where
  InterNil  :: IntertwinerSectors '[]
  InterCons :: KnownNat m
            => C m
            -> IntertwinerSectors rest
            -> IntertwinerSectors ('(Zero, m) ': rest)

pattern InterBlock :: forall m. KnownNat m => C m -> IntertwinerSectors '[ '(Zero, m)]
pattern InterBlock block <- InterCons block InterNil
  where
    InterBlock block = InterCons block InterNil

{-# COMPLETE InterNil, InterCons #-}

instance Show (IntertwinerSectors hom) where
  show InterNil = "InterNil"
  show (InterCons block rest) =
    show block ++ " : " ++ show rest

newtype Intertwiner (r :: U1Rep) (q :: U1Rep) = MkIntertwiner
  { unIntertwiner :: IntertwinerSectors (HomSectorList r q)
  }
  deriving Show via (IntertwinerSectors (HomSectorList r q))

mkScalar :: Complex Double -> IntertwinerSectors '[ '(Zero, 1)]
mkScalar z = InterBlock (konst z)

scalarOf :: C 1 -> Complex Double
scalarOf v = extract v ! 0

-- | View a flat hom block as an @m × m@ matrix.
blockAsMat :: forall m h. (KnownNat m, KnownNat h, EndoHomDim m ~ h) => C h -> M m m
blockAsMat block = fromList (toList (extract block))

class BuildIdHom (hom :: [(Z, Nat)]) where
  idHom :: IntertwinerSectors hom

instance BuildIdHom '[] where
  idHom = InterNil

instance (KnownNat m, BuildIdHom rest) => BuildIdHom ('(Zero, m) ': rest) where
  idHom = InterCons (konst 1) (idHom @rest)

composeHom
  :: IntertwinerSectors hab
  -> IntertwinerSectors hbc
  -> IntertwinerSectors hom
composeHom InterNil _ = unsafeCoerce InterNil
composeHom _ InterNil = unsafeCoerce InterNil
composeHom (InterCons x xs) (InterCons y ys) =
  unsafeCoerce (InterCons (unsafeCoerce y * x) (composeHom xs ys))

compose
  :: (U1RepList a, U1RepList b, U1RepList c)
  => Intertwiner b c -> Intertwiner a b -> Intertwiner a c
compose (MkIntertwiner bc) (MkIntertwiner ab) =
  MkIntertwiner (composeHom ab bc)

mkIdHom :: forall a. (U1RepList a, BuildIdHom (HomSectorList a a)) => Intertwiner a a
mkIdHom = MkIntertwiner (idHom @(HomSectorList a a))

instance Category Intertwiner where
  type Object Intertwiner r =
    ( U1RepList r
    , BuildIdHom (HomSectorList r r)
    , KnownNat (RepDim r)
    )

  id = mkIdHom

  (.) = compose

-- | Representation space: one flat complex vector @C (RepDim r)@.
newtype ToC (r :: U1Rep) = ToC (C (RepDim r))

zeroRep :: KnownNat (RepDim r) => ToC r
zeroRep = ToC (konst 0)

u1PhaseFactor :: forall z. KnownZ z => Double -> Complex Double
u1PhaseFactor theta =
  exp ((0 :+ 1) * (fromIntegral (getZ @z) * theta :+ 0))

class ActsOnRep (rs :: U1Rep) where
  repLinear :: Double -> (ToC rs -+> ToC rs)

instance ActsOnRep '[] where
  repLinear _ = LinearFunction (\(ToC v) -> ToC v)

-- | One charge sector (any multiplicity): scale the whole @C (RepDim rs)@ block.
instance (KnownZ z, KnownNat m) => ActsOnRep ('(z, m) ': '[]) where
  repLinear theta = LinearFunction (\(ToC v) -> ToC (u1PhaseFactor @z theta *^ v))

class ApplyHom (hom :: [(Z, Nat)]) (r :: U1Rep) (q :: U1Rep) where
  applyHom :: IntertwinerSectors hom -> ToC r -> ToC q

instance
  {-# OVERLAPPING #-}
  (KnownNat (RepDim r), KnownNat (RepDim q)) => ApplyHom '[] r q where
  applyHom InterNil _ = zeroRep

instance
  {-# OVERLAPPING #-}
  KnownZ z => ApplyHom '[ '(Zero, 1)] '[ '(z, 1)] '[ '(z, 1)] where
  applyHom (InterCons block InterNil) (ToC v) =
    ToC (scalarOf block *^ v)

-- | Endomorphism of a single charge sector with multiplicity @m@.
instance
  {-# OVERLAPPING #-}
  (KnownNat m, KnownNat h, EndoHomDim m ~ h)
  => ApplyHom '[ '(Zero, h)] '[ '(z, m)] '[ '(z, m)] where
  applyHom (InterCons block InterNil) (ToC v) =
    ToC (app (blockAsMat @m block) v)

instance
  {-# INCOHERENT #-}
  (U1RepList r, U1RepList q, KnownNat (RepDim r), KnownNat (RepDim q))
  => ApplyHom hom r q where
  applyHom InterNil _ = zeroRep
  applyHom (InterCons _ _) _ =
    error "ApplyHom: unimplemented hom block layout"

intertwinerLinear
  :: forall r q.
     ( U1RepList r, U1RepList q
     , ApplyHom (HomSectorList r q) r q
     )
  => Intertwiner r q
  -> LinearFunction (Complex Double) (ToC r) (ToC q)
intertwinerLinear (MkIntertwiner sectors) =
  LinearFunction (applyHom sectors)

instance
  ( U1RepList r, U1RepList q
  ) => Functor ToC Intertwiner (LinearFunction (Complex Double)) where
  fmap = intertwinerLinear

-- | @TensorSpace@ delegates to flat @C (RepDim r)@ (no @HList@).
instance KnownNat (RepDim r) => AdditiveGroup (ToC r) where
  ToC a ^+^ ToC b = ToC (a ^+^ b)
  zeroV = ToC zeroV
  negateV (ToC v) = ToC (negateV v)

instance KnownNat (RepDim r) => VectorSpace (ToC r) where
  type Scalar (ToC r) = Complex Double
  μ *^ ToC v = ToC (μ *^ v)

instance KnownNat (RepDim r) => InnerSpace (ToC r) where
  ToC v <.> ToC w = v <.> w

instance KnownNat (RepDim r) => DimensionAware (ToC r) where
  type StaticDimension (ToC r) = StaticDimension (C (RepDim r))
  dimensionalityWitness = undefined

instance (KnownNat (RepDim r), n ~ RepDim r) => n `Dimensional` ToC r where
  knownDimensionalitySing = sing
  unsafeFromArrayWithOffset i ar =
    ToC (unsafeFromArrayWithOffset i ar)
  unsafeWriteArrayWithOffset ar i (ToC v) =
    unsafeWriteArrayWithOffset ar i v

instance KnownNat (RepDim r) => Semimanifold (ToC r) where
  type Needle (ToC r) = C (RepDim r)
  ToC _ .+~^ _ = undefined

instance KnownNat (RepDim r) => PseudoAffine (ToC r) where
  ToC _ .-~! ToC _ = undefined
  ToC _ .-~. ToC _ = undefined

instance KnownNat (RepDim r) => TensorSpace (ToC r) where
  type TensorProduct (ToC r) w = TensorProduct (C (RepDim r)) w
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
  wellDefinedVector (ToC v) = ToC <$> wellDefinedVector v
  wellDefinedTensor = undefined
  vectorConjugate = undefined

instance KnownNat (RepDim r) => Eq (ToC r) where
  ToC a == ToC b = a == b

instance KnownNat (RepDim r) => Show (ToC r) where
  show (ToC v) = show v

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

type Pos1       = '[ '(Pos 1, 1)]
type ZeroRep    = '[ '(Zero, 1)]
type DoublePos1 = '[ '(Pos 1, 2)]

type ZeroToOneHom  = HomSectorList ZeroRep Pos1
type PhaseHom      = HomSectorList Pos1 Pos1
type NegPosHom     = HomSectorList ('[ '(('Neg 1), 1)]) Pos1
type DoublePos1Hom = HomSectorList DoublePos1 DoublePos1

zeroToOneEmpty :: (ZeroToOneHom ~ '[]) => ()
zeroToOneEmpty = ()

phaseHom :: (PhaseHom ~ '[ '(Zero, 1)]) => ()
phaseHom = ()

negPosHom :: (NegPosHom ~ '[]) => ()
negPosHom = ()

doublePos1Hom :: (DoublePos1Hom ~ '[ '(Zero, 4)]) => ()
doublePos1Hom = ()

zeroToOne :: Intertwiner ZeroRep Pos1
zeroToOne = MkIntertwiner InterNil

phase :: Intertwiner Pos1 Pos1
phase = MkIntertwiner (mkScalar (0 :+ 1))

phaseSquared :: Intertwiner Pos1 Pos1
phaseSquared = phase . phase

repSpace1 :: ToC Pos1
repSpace1 = ToC (konst 1)

repDoublePos1 :: ToC DoublePos1
repDoublePos1 = ToC (konst 1)

phaseLinear :: LinearFunction (Complex Double) (ToC Pos1) (ToC Pos1)
phaseLinear = intertwinerLinear (phase :: Intertwiner Pos1 Pos1)

testPhaseSquared :: ToC Pos1
testPhaseSquared = getLinearFunction (intertwinerLinear phaseSquared) repSpace1

phaseLinearFromAction :: LinearFunction (Complex Double)
  (ToC Pos1) (ToC Pos1)
phaseLinearFromAction = repLinear @Pos1 (pi / 2)

composedLinearAction :: LinearFunction (Complex Double)
  (ToC Pos1) (ToC Pos1)
composedLinearAction = repLinear @Pos1 1 . repLinear @Pos1 2

-- | Endo intertwiner with one @4@-dimensional hom block (@2 × 2@ matrix on @C 2@).
doublePos1Inter :: Intertwiner '[ '(Pos 1, 2)] '[ '(Pos 1, 2)]
doublePos1Inter = MkIntertwiner (InterBlock (konst 1))

testDoublePos1 :: ToC DoublePos1
testDoublePos1 = getLinearFunction (intertwinerLinear doublePos1Inter) repDoublePos1
