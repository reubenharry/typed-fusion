{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Leaf / multiplicity-block fusion experiments.
--
-- Type-level fusion spines are 'Tensor' (@Coalesce ∘ TensorRaw@). In particular
--
--   @FuseSectors g x y = Tensor g '[x] '[y]@
--
-- so 'FuseMN' carries @RepToVectors g (Tensor g '[x] '[y])@. Hom packing is
-- @FilterNonTrivial (Tensor (DualRep r) q)@.
--
-- Term-level: 'fuseMN' = @recompose . f . decompose@ with flat CG as the matrix;
-- 'rmoveMN' / 'swapUnfuseMN' braid fused / unfused sides.
--
-- Examples: 'Experiments.GeneralExamples'.
module Experiments.General where

import Control.Arrow (first)
import Control.Arrow.Constrained (arr, ($))
import Control.Category.Constrained (id)
import Control.Category.Constrained.Prelude (Category (..))
import Data.Basis (HasBasis (..), recompose)
import Data.Complex (Complex (..))
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Data.Singletons (SingI)
import Data.Singletons.TH (genSingletons)
import Data.VectorSpace (AdditiveGroup (..), InnerSpace ((<.>)), VectorSpace (..), (*^), sumV)
import Data.Void (Void, absurd)
import Experiments.Experiment2 (Multiplicity)
import Experiments.SU2 (TensorIrrepRepSU2)
import GHC.TypeLits (CmpNat, KnownNat, Nat, natVal, type (+))
import Math.LinearMap.Asserted (linearFunction)
import Math.LinearMap.Category
  ( LSpace
  , Scalar
  , TensorSpace
  , type (+>)
  , type (⊗)
  , (⊗)
  )
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import Numeric.LinearAlgebra.Static (C, Sized (fromList))
import Prelude hiding (id, (.), ($))
import qualified Symmetry.Group as SG
import Symmetry.CG.SU2 (fuseSU2Flat)
import Symmetry.CG.U1 (fuseU1Flat)
import Symmetry.ChargeEq ()
import Symmetry.RepSingleton (KnownRep (..))
import Symmetry.Utils
  ( Add
  , Append
  , HList (..)
  , HMap (..)
  , HPure (..)
  , HZipWith (..)
  , Negate
  , Scale
  , Z (..)
  )
import TensorNetwork.Categorical ((⊗^), swapMap)
import qualified Data.Vector.Storable as VS

--------------------------------------------------------------------------------
-- Groups, irreps, sectors
--------------------------------------------------------------------------------

data Group = U1 | SU2
$(genSingletons [''Group])

type family Irreps (g :: Group) :: Type where
  Irreps U1 = Z
  Irreps SU2 = Nat

type IrrepDim :: forall (g :: Group) -> Irreps g -> Nat
type family IrrepDim g p where
  IrrepDim U1 p = 1
  IrrepDim SU2 p = p + 1

newtype Irrep (g :: Group) (p :: Irreps g) =
  Irrep { unGIrrep :: C (IrrepDim g p) }

deriving instance KnownNat (IrrepDim g p) => Show (Irrep g p)
deriving newtype instance KnownNat (IrrepDim g p) => AdditiveGroup (Irrep g p)

type Sector :: forall (g :: Group) -> Irreps g -> Multiplicity -> Type
type family Sector g j m where
  Sector U1 (j :: Z) m = C m ⊗ C (IrrepDim U1 j)
  Sector SU2 (j :: Nat) m = C m ⊗ C (IrrepDim SU2 j)

type RepToVectors :: forall (g :: Group) -> [(Irreps g, Multiplicity)] -> [Type]
type family RepToVectors g rs where
  RepToVectors U1 '[] = '[]
  RepToVectors SU2 '[] = '[]
  RepToVectors U1 ('(j, m) ': rs) = Sector U1 j m ': RepToVectors U1 rs
  RepToVectors SU2 ('(j, m) ': rs) = Sector SU2 j m ': RepToVectors SU2 rs

newtype Representation (g :: Group) (r :: [(Irreps g, Multiplicity)]) =
  Representation (HList (RepToVectors g r))

type TensorIrrepRep :: forall (g :: Group) -> Irreps g -> Irreps g -> [(Irreps g, Multiplicity)]
type family TensorIrrepRep g j1 j2 where
  TensorIrrepRep SU2 j1 j2 = TensorIrrepRepSU2 j1 j2
  TensorIrrepRep U1 j1 j2 = '[ '(Add j1 j2, 1) ]

type family ScaleRep (s :: Multiplicity) (xs :: [(k, Multiplicity)])
  :: [(k, Multiplicity)] where
  ScaleRep _ '[] = '[]
  ScaleRep s ('(j, n) ': xs) = '(j, Scale s n) ': ScaleRep s xs

--------------------------------------------------------------------------------
-- Type-level Tensor: Coalesce ∘ TensorRaw (Distribute + leaf CG + scale)
--
-- This is the fusion spine used by 'FuseMN', Hom packing, etc.
--------------------------------------------------------------------------------

type DualIrrep :: forall (g :: Group) -> Irreps g -> Irreps g
type family DualIrrep g p where
  DualIrrep U1 q = Negate q
  DualIrrep SU2 j = j

type DualRep :: forall (g :: Group) -> [(Irreps g, Multiplicity)] -> [(Irreps g, Multiplicity)]
type family DualRep g r where
  DualRep U1 '[] = '[]
  DualRep SU2 '[] = '[]
  DualRep U1 ('(i, m) ': rs) = '(DualIrrep U1 i, m) ': DualRep U1 rs
  DualRep SU2 ('(i, m) ': rs) = '(DualIrrep SU2 i, m) ': DualRep SU2 rs

-- | Uncoalesced CG branching (left × right, Append order).
type TensorRaw
  :: forall (g :: Group)
  -> [(Irreps g, Multiplicity)]
  -> [(Irreps g, Multiplicity)]
  -> [(Irreps g, Multiplicity)]
type family TensorRaw g r q where
  TensorRaw U1 '[] _ = '[]
  TensorRaw SU2 '[] _ = '[]
  TensorRaw U1 ('(i, m) ': rs) q =
    Append (TensorOne U1 '(i, m) q) (TensorRaw U1 rs q)
  TensorRaw SU2 ('(i, m) ': rs) q =
    Append (TensorOne SU2 '(i, m) q) (TensorRaw SU2 rs q)

type TensorOne
  :: forall (g :: Group)
  -> (Irreps g, Multiplicity)
  -> [(Irreps g, Multiplicity)]
  -> [(Irreps g, Multiplicity)]
type family TensorOne g x q where
  TensorOne U1 _ '[] = '[]
  TensorOne U1 '(i, m) ('(j, n) ': qs) =
    '(Add i j, Scale m n) ': TensorOne U1 '(i, m) qs
  TensorOne SU2 _ '[] = '[]
  TensorOne SU2 '(i, m) ('(j, n) ': qs) =
    Append
      (ScaleRep (Scale m n) (TensorIrrepRep SU2 i j))
      (TensorOne SU2 '(i, m) qs)

type Coalesce
  :: forall (g :: Group) -> [(Irreps g, Multiplicity)] -> [(Irreps g, Multiplicity)]
type family Coalesce g r where
  Coalesce U1 r = CoalesceU1 r
  Coalesce SU2 r = CoalesceSU2 r

type family CoalesceU1 (r :: [(Z, Multiplicity)]) :: [(Z, Multiplicity)] where
  CoalesceU1 '[] = '[]
  CoalesceU1 ('(j, m) ': rest) = InsertSectorU1 j m (CoalesceU1 rest)

type family CoalesceSU2 (r :: [(Nat, Multiplicity)]) :: [(Nat, Multiplicity)] where
  CoalesceSU2 '[] = '[]
  CoalesceSU2 ('(j, m) ': rest) = InsertSectorSU2 j m (CoalesceSU2 rest)

type family InsertSectorU1 j m r where
  InsertSectorU1 j m '[] = '[ '(j, m)]
  InsertSectorU1 j m ('(j2, n) ': rest) =
    InsertSectorZ (CmpZ j j2) j m j2 n rest

type family InsertSectorSU2 j m r where
  InsertSectorSU2 j m '[] = '[ '(j, m)]
  InsertSectorSU2 j m ('(j2, n) ': rest) =
    InsertSectorNat (CmpNat j j2) j m j2 n rest

type family InsertSectorNat o j m j2 n rest where
  InsertSectorNat 'EQ j m _ n rest = '(j, m + n) ': rest
  InsertSectorNat 'LT j m j2 n rest = '(j, m) ': '(j2, n) ': rest
  InsertSectorNat 'GT j m j2 n rest = '(j2, n) ': InsertSectorSU2 j m rest

type family InsertSectorZ o j m j2 n rest where
  InsertSectorZ 'EQ j m _ n rest = '(j, m + n) ': rest
  InsertSectorZ 'LT j m j2 n rest = '(j, m) ': '(j2, n) ': rest
  InsertSectorZ 'GT j m j2 n rest = '(j2, n) ': InsertSectorU1 j m rest

type family CmpZ (a :: Z) (b :: Z) :: Ordering where
  CmpZ 'Zero 'Zero = 'EQ
  CmpZ 'Zero ('Pos _) = 'LT
  CmpZ 'Zero ('Neg _) = 'GT
  CmpZ ('Pos _) 'Zero = 'GT
  CmpZ ('Neg _) 'Zero = 'LT
  CmpZ ('Pos a) ('Pos b) = CmpNat a b
  CmpZ ('Neg a) ('Neg b) = CmpNat b a
  CmpZ ('Neg _) ('Pos _) = 'LT
  CmpZ ('Pos _) ('Neg _) = 'GT

-- | Fused + coalesced spine @r ⊗ q@.
type Tensor
  :: forall (g :: Group)
  -> [(Irreps g, Multiplicity)]
  -> [(Irreps g, Multiplicity)]
  -> [(Irreps g, Multiplicity)]
type family Tensor g r q where
  Tensor g r q = Coalesce g (TensorRaw g r q)

-- | Trivial-channel projection (Hom packing / evaluation).
type FilterNonTrivial
  :: forall (g :: Group) -> [(Irreps g, Multiplicity)] -> [(Irreps g, Multiplicity)]
type family FilterNonTrivial g r where
  FilterNonTrivial U1 '[] = '[]
  FilterNonTrivial U1 ('( 'Zero, m) ': rs) =
    '( 'Zero, m) ': FilterNonTrivial U1 rs
  FilterNonTrivial U1 ('(i, m) ': rs) = FilterNonTrivial U1 rs
  FilterNonTrivial SU2 '[] = '[]
  FilterNonTrivial SU2 ('(0, m) ': rs) =
    '(0, m) ': FilterNonTrivial SU2 rs
  FilterNonTrivial SU2 ('(i, m) ': rs) = FilterNonTrivial SU2 rs

-- | Hom space as trivial sector of @Dual r ⊗ q@.
type family (a :: Type) `Intertwiner` (b :: Type) :: Type where
  (Representation g r) `Intertwiner` (Representation g q) =
    HList (RepToVectors g (FilterNonTrivial g (Tensor g (DualRep g r) q)))

-- | Single-sector fusion spine = type-level 'Tensor' of singleton spines.
type FuseSectors
  :: forall (g :: Group)
  -> (Irreps g, Multiplicity)
  -> (Irreps g, Multiplicity)
  -> [(Irreps g, Multiplicity)]
type family FuseSectors g x y where
  FuseSectors g x y = Tensor g '[x] '[y]

-- | Leaf fused pair (multiplicity 1). Prefer 'FuseMN' when @m,n > 1@.
newtype Fuse (g :: Group) (a :: Irreps g) (b :: Irreps g) =
  Fuse { unFuse :: Representation g (Tensor g '[ '(a, 1)] '[ '(b, 1)]) }

type family Fst (p :: (k, l)) :: k where
  Fst '(a, _) = a

type family Snd (p :: (k, l)) :: l where
  Snd '(_, b) = b

--------------------------------------------------------------------------------
-- HList vector-space / basis (direct sum)
--------------------------------------------------------------------------------

class (VectorSpace v, Scalar v ~ Complex Double) => VsC v
instance (VectorSpace v, Scalar v ~ Complex Double) => VsC v

class HHasBasis (xs :: [Type]) where
  type HBasis xs :: Type
  hBasisValue :: HBasis xs -> HList xs
  hDecompose :: HList xs -> [(HBasis xs, Complex Double)]
  hDecompose' :: HList xs -> HBasis xs -> Complex Double

instance HHasBasis '[] where
  type HBasis '[] = Void
  hBasisValue = absurd
  hDecompose HNil = []
  hDecompose' HNil = absurd

instance
  ( HasBasis x
  , Scalar x ~ Complex Double
  , AdditiveGroup x
  , HHasBasis xs
  , HPure AdditiveGroup xs
  ) =>
  HHasBasis (x ': xs)
  where
  type HBasis (x ': xs) = Either (Basis x) (HBasis xs)
  hBasisValue (Left b) =
    basisValue b :& hpureC (Proxy @AdditiveGroup) zeroV
  hBasisValue (Right b) =
    zeroV :& hBasisValue b
  hDecompose (x :& xs) =
    map (first Left) (decompose x)
      ++ map (first Right) (hDecompose xs)
  hDecompose' (x :& xs) =
    either (decompose' x) (hDecompose' xs)

--------------------------------------------------------------------------------
-- UnfuseMN / FuseMN
--------------------------------------------------------------------------------

-- | Unfused @m·V_a ⊗ n·V_b@.
newtype UnfuseMN g x y =
  UnfuseMN
    { unUnfuseMN :: Sector g (Fst x) (Snd x) ⊗ Sector g (Fst y) (Snd y)
    }

instance
  ( AdditiveGroup
      (Sector g (Fst x) (Snd x) ⊗ Sector g (Fst y) (Snd y))
  ) =>
  AdditiveGroup (UnfuseMN g x y)
  where
  zeroV = UnfuseMN zeroV
  UnfuseMN a ^+^ UnfuseMN b = UnfuseMN (a ^+^ b)
  negateV (UnfuseMN a) = UnfuseMN (negateV a)

instance
  ( VectorSpace
      (Sector g (Fst x) (Snd x) ⊗ Sector g (Fst y) (Snd y))
  , Scalar (Sector g (Fst x) (Snd x) ⊗ Sector g (Fst y) (Snd y))
      ~ Complex Double
  ) =>
  VectorSpace (UnfuseMN g x y)
  where
  type Scalar (UnfuseMN g x y) = Complex Double
  μ *^ UnfuseMN a = UnfuseMN (μ *^ a)

instance
  ( HasBasis
      (Sector g (Fst x) (Snd x) ⊗ Sector g (Fst y) (Snd y))
  , Scalar (Sector g (Fst x) (Snd x) ⊗ Sector g (Fst y) (Snd y))
      ~ Complex Double
  ) =>
  HasBasis (UnfuseMN g x y)
  where
  type Basis (UnfuseMN g x y) =
    Basis (Sector g (Fst x) (Snd x) ⊗ Sector g (Fst y) (Snd y))
  basisValue b = UnfuseMN (basisValue b)
  decompose (UnfuseMN t) = decompose t
  decompose' (UnfuseMN t) = decompose' t

-- | Fused @m·V_a ⊗ n·V_b@: payload @RepToVectors g (Tensor g '[x] '[y])@.
newtype FuseMN g x y =
  FuseMN { unFuseMN :: HList (RepToVectors g (FuseSectors g x y)) }

instance
  ( HPure AdditiveGroup (RepToVectors g (FuseSectors g x y))
  , HMap AdditiveGroup (RepToVectors g (FuseSectors g x y))
  , HZipWith AdditiveGroup (RepToVectors g (FuseSectors g x y))
  ) =>
  AdditiveGroup (FuseMN g x y)
  where
  zeroV = FuseMN $ hpureC (Proxy @AdditiveGroup) zeroV
  FuseMN xs ^+^ FuseMN ys =
    FuseMN $ hzipWithC (Proxy @AdditiveGroup) (^+^) xs ys
  negateV (FuseMN xs) =
    FuseMN $ hmapC (Proxy @AdditiveGroup) negateV xs

instance
  ( HPure VsC (RepToVectors g (FuseSectors g x y))
  , HMap VsC (RepToVectors g (FuseSectors g x y))
  , HZipWith VsC (RepToVectors g (FuseSectors g x y))
  , HPure AdditiveGroup (RepToVectors g (FuseSectors g x y))
  , HMap AdditiveGroup (RepToVectors g (FuseSectors g x y))
  , HZipWith AdditiveGroup (RepToVectors g (FuseSectors g x y))
  ) =>
  VectorSpace (FuseMN g x y)
  where
  type Scalar (FuseMN g x y) = Complex Double
  μ *^ FuseMN xs = FuseMN $ hmapC (Proxy @VsC) (μ *^) xs

instance
  ( HHasBasis (RepToVectors g (FuseSectors g x y))
  , HPure VsC (RepToVectors g (FuseSectors g x y))
  , HMap VsC (RepToVectors g (FuseSectors g x y))
  , HZipWith VsC (RepToVectors g (FuseSectors g x y))
  , HPure AdditiveGroup (RepToVectors g (FuseSectors g x y))
  , HMap AdditiveGroup (RepToVectors g (FuseSectors g x y))
  , HZipWith AdditiveGroup (RepToVectors g (FuseSectors g x y))
  ) =>
  HasBasis (FuseMN g x y)
  where
  type Basis (FuseMN g x y) = HBasis (RepToVectors g (FuseSectors g x y))
  basisValue b = FuseMN (hBasisValue b)
  decompose (FuseMN xs) = hDecompose xs
  decompose' (FuseMN xs) = hDecompose' xs

--------------------------------------------------------------------------------
-- Constructors / helpers
--------------------------------------------------------------------------------

stdBasisC :: forall k. KnownNat k => Int -> C k
stdBasisC i =
  let d = fromIntegral (natVal (Proxy @k)) :: Int
  in  fromList [ if j == i then 1 else 0 | j <- [0 .. d - 1] ]

packMultIrrep
  :: forall k d. (KnownNat k, KnownNat d)
  => [C d]
  -> C k ⊗ C d
packMultIrrep vs =
  sumV [ stdBasisC @k i ⊗ v | (i, v) <- zip [0 ..] vs ]

asSector1
  :: forall g j.
     ( Sector g j 1 ~ (C 1 ⊗ C (IrrepDim g j))
     , KnownNat (IrrepDim g j)
     )
  => Irrep g j
  -> Sector g j 1
asSector1 (Irrep c) = (fromList [1] :: C 1) ⊗ c

tensorSectors
  :: forall g a m b n.
     ( KnownNat m
     , KnownNat n
     , KnownNat (IrrepDim g a)
     , KnownNat (IrrepDim g b)
     , Sector g a m ~ (C m ⊗ C (IrrepDim g a))
     , Sector g b n ~ (C n ⊗ C (IrrepDim g b))
     )
  => Sector g a m
  -> Sector g b n
  -> UnfuseMN g '(a, m) '(b, n)
tensorSectors ua vb = UnfuseMN (ua ⊗ vb)

swapUnfuseMN
  :: forall g a m b n.
     ( KnownNat m
     , KnownNat n
     , KnownNat (IrrepDim g a)
     , KnownNat (IrrepDim g b)
     , Sector g a m ~ (C m ⊗ C (IrrepDim g a))
     , Sector g b n ~ (C n ⊗ C (IrrepDim g b))
     )
  => UnfuseMN g '(a, m) '(b, n)
  -> UnfuseMN g '(b, n) '(a, m)
swapUnfuseMN (UnfuseMN t) = UnfuseMN (swapMap $ t)

--------------------------------------------------------------------------------
-- fuseMN = recompose . f . decompose
--------------------------------------------------------------------------------

-- | Unpack flat fused buffer into typed sectors (mult slow, irrep fast).
class UnpackFusedFlat g (rs :: [(Irreps g, Multiplicity)]) where
  unpackFusedFlat :: VS.Vector (Complex Double) -> HList (RepToVectors g rs)

instance UnpackFusedFlat U1 '[] where
  unpackFusedFlat _ = HNil

instance UnpackFusedFlat SU2 '[] where
  unpackFusedFlat _ = HNil

instance
  ( KnownNat m
  , KnownNat (IrrepDim U1 j)
  , UnpackFusedFlat U1 rs
  , RepToVectors U1 ('(j, m) ': rs)
      ~ (Sector U1 j m ': RepToVectors U1 rs)
  ) =>
  UnpackFusedFlat U1 ('(j, m) ': rs)
  where
  unpackFusedFlat flat =
    let d =
          fromIntegral (natVal (Proxy @m))
            * fromIntegral (natVal (Proxy @(IrrepDim U1 j)))
        (here, rest) = VS.splitAt d flat
    in  unsafeFromArray here :& unpackFusedFlat @U1 @rs rest

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim SU2 j)
  , UnpackFusedFlat SU2 rs
  , RepToVectors SU2 ('(j, m) ': rs)
      ~ (Sector SU2 j m ': RepToVectors SU2 rs)
  ) =>
  UnpackFusedFlat SU2 ('(j, m) ': rs)
  where
  unpackFusedFlat flat =
    let d =
          fromIntegral (natVal (Proxy @m))
            * fromIntegral (natVal (Proxy @(IrrepDim SU2 j)))
        (here, rest) = VS.splitAt d flat
    in  unsafeFromArray here :& unpackFusedFlat @SU2 @rs rest

-- | Flat CG matrix on coefficient buffers (the intertwiner Φ).
class CanFuseMN g x y where
  fuseMNFlat :: UnfuseMN g x y -> FuseMN g x y
  fuseMN :: UnfuseMN g x y -> FuseMN g x y

instance
  ( KnownNat a
  , KnownNat b
  , KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim SU2 a)
  , KnownNat (IrrepDim SU2 b)
  , KnownRep SG.SU2 '[ '(a, m) ]
  , KnownRep SG.SU2 '[ '(b, n) ]
  , UnpackFusedFlat SU2 (FuseSectors SU2 '(a, m) '(b, n))
  , Sector SU2 a m ~ (C m ⊗ C (IrrepDim SU2 a))
  , Sector SU2 b n ~ (C n ⊗ C (IrrepDim SU2 b))
  , HasBasis (UnfuseMN SU2 '(a, m) '(b, n))
  , HasBasis (FuseMN SU2 '(a, m) '(b, n))
  , Scalar (UnfuseMN SU2 '(a, m) '(b, n)) ~ Complex Double
  , Scalar (FuseMN SU2 '(a, m) '(b, n)) ~ Complex Double
  ) =>
  CanFuseMN SU2 '(a, m) '(b, n)
  where
  fuseMNFlat (UnfuseMN t) =
    FuseMN $
      unpackFusedFlat @SU2 @(FuseSectors SU2 '(a, m) '(b, n)) $
        fuseSU2Flat
          (repSing @SG.SU2 @'[ '(a, m) ])
          (repSing @SG.SU2 @'[ '(b, n) ])
          (toArray t)
  fuseMN u =
    (recompose . f . decompose) u
    where
      f coeffs =
        concatMap
          ( \(b, c) ->
              [ (b', c * a)
              | (b', a) <-
                  decompose @(FuseMN SU2 '(a, m) '(b, n))
                    (fuseMNFlat (basisValue b))
              ]
          )
          coeffs

instance
  ( KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim U1 a)
  , KnownNat (IrrepDim U1 b)
  , SingI a
  , SingI b
  , KnownRep SG.U1 '[ '(a, m) ]
  , KnownRep SG.U1 '[ '(b, n) ]
  , UnpackFusedFlat U1 (FuseSectors U1 '(a, m) '(b, n))
  , Sector U1 a m ~ (C m ⊗ C (IrrepDim U1 a))
  , Sector U1 b n ~ (C n ⊗ C (IrrepDim U1 b))
  , HasBasis (UnfuseMN U1 '(a, m) '(b, n))
  , HasBasis (FuseMN U1 '(a, m) '(b, n))
  , Scalar (UnfuseMN U1 '(a, m) '(b, n)) ~ Complex Double
  , Scalar (FuseMN U1 '(a, m) '(b, n)) ~ Complex Double
  ) =>
  CanFuseMN U1 '(a, m) '(b, n)
  where
  fuseMNFlat (UnfuseMN t) =
    FuseMN $
      unpackFusedFlat @U1 @(FuseSectors U1 '(a, m) '(b, n)) $
        fuseU1Flat
          (repSing @SG.U1 @'[ '(a, m) ])
          (repSing @SG.U1 @'[ '(b, n) ])
          (toArray t)
  fuseMN u =
    (recompose . f . decompose) u
    where
      f coeffs =
        concatMap
          ( \(b, c) ->
              [ (b', c * a)
              | (b', a) <-
                  decompose @(FuseMN U1 '(a, m) '(b, n))
                    (fuseMNFlat (basisValue b))
              ]
          )
          coeffs

--------------------------------------------------------------------------------
-- rmoveMN
--------------------------------------------------------------------------------

rPhaseScalar
  :: forall j1 j2 j. (KnownNat j1, KnownNat j2, KnownNat j)
  => Complex Double
rPhaseScalar =
  let tj1 = fromIntegral (natVal (Proxy @j1)) :: Int
      tj2 = fromIntegral (natVal (Proxy @j2))
      tj = fromIntegral (natVal (Proxy @j))
  in  ((-1) ^ ((tj1 + tj2 - tj) `div` 2)) :+ 0

rPhaseSector
  :: forall j1 j2 j k.
     ( KnownNat j1
     , KnownNat j2
     , KnownNat j
     , KnownNat k
     , KnownNat (IrrepDim SU2 j)
     )
  => Sector SU2 j k
  -> Sector SU2 j k
rPhaseSector = (rPhaseScalar @j1 @j2 @j *^)

-- | Transpose @m × n@ copy indices on @ℂ^{m·n}@.
swapCopyGridMN
  :: forall m n. (KnownNat m, KnownNat n, KnownNat (Scale m n))
  => C (Scale m n)
  -> C (Scale m n)
swapCopyGridMN c =
  sumV
    [ (c <.> stdBasisC @(Scale m n) idxIn)
        *^ stdBasisC @(Scale m n) idxOut
    | iUa <- [0 .. m' - 1]
    , iVb <- [0 .. n' - 1]
    , let idxIn = iVb + n' * iUa
          idxOut = iUa + m' * iVb
    ]
  where
    m' = fromIntegral (natVal (Proxy @m))
    n' = fromIntegral (natVal (Proxy @n))

swapCopyGridSector
  :: forall m n d.
     ( KnownNat m
     , KnownNat n
     , KnownNat d
     , KnownNat (Scale m n)
     , LSpace (C (Scale m n))
     , LSpace (C d)
     , LSpace (C (Scale m n) ⊗ C d)
     , TensorSpace (C (Scale m n) ⊗ C d)
     , Scalar (C (Scale m n)) ~ Complex Double
     , Scalar (C d) ~ Complex Double
     )
  => C (Scale m n) ⊗ C d
  -> C (Scale m n) ⊗ C d
swapCopyGridSector sec =
  (arr (linearFunction (swapCopyGridMN @m @n)) ⊗^ (id :: C d +> C d)) $ sec

-- | Per-channel R-phase + copy-grid swap (SU(2) fused braiding).
class MapRmoveSU2 m n j1 j2 (chs :: [(Nat, Multiplicity)]) where
  mapRmoveSU2 :: HList (RepToVectors SU2 chs) -> HList (RepToVectors SU2 chs)

instance MapRmoveSU2 m n j1 j2 '[] where
  mapRmoveSU2 HNil = HNil

instance
  ( KnownNat m
  , KnownNat n
  , KnownNat j1
  , KnownNat j2
  , KnownNat j
  , KnownNat k
  , k ~ Scale m n
  , KnownNat (IrrepDim SU2 j)
  , MapRmoveSU2 m n j1 j2 rs
  , RepToVectors SU2 ('(j, k) ': rs)
      ~ (Sector SU2 j k ': RepToVectors SU2 rs)
  ) =>
  MapRmoveSU2 m n j1 j2 ('(j, k) ': rs)
  where
  mapRmoveSU2 (sec :& rest) =
    swapCopyGridSector @m @n @(IrrepDim SU2 j)
      (rPhaseSector @j1 @j2 @j @k sec)
      :& mapRmoveSU2 @m @n @j1 @j2 @rs rest

class CanRmoveMN g x y where
  rmoveMN :: FuseMN g x y -> FuseMN g y x

instance
  ( Scale m n ~ Scale n m
  , FuseSectors U1 '(a, m) '(b, n) ~ FuseSectors U1 '(b, n) '(a, m)
  ) =>
  CanRmoveMN U1 '(a, m) '(b, n)
  where
  rmoveMN (FuseMN hs) = FuseMN hs

instance
  ( KnownNat a
  , KnownNat b
  , KnownNat m
  , KnownNat n
  , Scale m n ~ Scale n m
  , FuseSectors SU2 '(a, m) '(b, n) ~ FuseSectors SU2 '(b, n) '(a, m)
  , MapRmoveSU2 m n a b (FuseSectors SU2 '(a, m) '(b, n))
  ) =>
  CanRmoveMN SU2 '(a, m) '(b, n)
  where
  rmoveMN (FuseMN hs) =
    FuseMN (mapRmoveSU2 @m @n @a @b @(FuseSectors SU2 '(a, m) '(b, n)) hs)
