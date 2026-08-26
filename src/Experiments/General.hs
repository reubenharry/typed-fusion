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
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{- HLINT ignore "Eta reduce" -}

-- | Leaf / multiplicity-block fusion experiments.
--
-- Repss carry real copy spaces: 'Atom' @m = C m@, 'Prod' @m n = C m ⊗ C n@.
-- 'Sector' is @copy ⊗ irrep@. Flat CG uses 'DimOf' (@StaticDimension@).
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
import GHC.TypeLits (CmpNat, KnownNat, Nat, natVal, type (+), type (*))
import Math.LinearMap.Category
  ( LSpace
  , Scalar
  , TensorSpace
  , type (+>)
  , type (⊗)
  , (⊗)
  )
import qualified Math.LinearMap.Category as LM (Tensor (..))
import Math.VectorSpace.DimensionAware
  ( DimensionAware (..)
  , toArray
  , unsafeFromArray
  )
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
  , Negate
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

type ℂ = Complex Double

-- | Atom copy space: bare multiplicity @C m@ (distinct from 'Prod').
type Atom (m :: Nat) = C m

-- | Product copy space @C m ⊗ C n@ (concrete 'LM.Tensor' so closed TFs can match;
-- @⊗@ expands via 'Scalar' and is illegal in TF / instance heads).
type Prod (m :: Nat) (n :: Nat) = LM.Tensor ℂ (C m) (C n)

type family FromJust (m :: Maybe Nat) :: Nat where
  FromJust ('Just n) = n

-- | Static dimension of a copy (or any) space via 'StaticDimension'.
type DimOf (v :: Type) = FromJust (StaticDimension v)

type MultipleIrreps g = (Irreps g, Type)
type Reps g = [MultipleIrreps g]

newtype Irrep (g :: Group) (p :: Irreps g) =
  Irrep { unGIrrep :: C (IrrepDim g p) }

deriving instance KnownNat (IrrepDim g p) => Show (Irrep g p)
deriving newtype instance KnownNat (IrrepDim g p) => AdditiveGroup (Irrep g p)

-- | Sector = copy space ⊗ irrep carrier.
type Sector g j copy = copy ⊗ C (IrrepDim g j)

-- | Swap factors of a product copy space; atoms @C m@ are unchanged.
type family BraidCopy (v :: Type) :: Type where
  BraidCopy (LM.Tensor s (C m) (C n)) = LM.Tensor s (C n) (C m)
  BraidCopy (C m) = C m
  BraidCopy v = v

type family BraidReps g (rs :: Reps g) :: Reps g where
  BraidReps U1 '[] = '[]
  BraidReps U1 ('(j, copy) ': rs) =
    '(j, BraidCopy copy) ': BraidReps U1 rs
  BraidReps SU2 '[] = '[]
  BraidReps SU2 ('(j, copy) ': rs) =
    '(j, BraidCopy copy) ': BraidReps SU2 rs

type RepToVectors :: forall (g :: Group) -> Reps g -> [Type]
type family RepToVectors g rs where
  RepToVectors U1 '[] = '[]
  RepToVectors U1 ('(j, copy) ': rs) = Sector U1 j copy ': RepToVectors U1 rs
  RepToVectors SU2 '[] = '[]
  RepToVectors SU2 ('(j, copy) ': rs) = Sector SU2 j copy ': RepToVectors SU2 rs

newtype Representation (g :: Group) (r :: Reps g) =
  Representation (HList (RepToVectors g r))

type TensorIrrepRep :: forall (g :: Group) -> Irreps g -> Irreps g -> [(Irreps g, Multiplicity)]
type family TensorIrrepRep g j1 j2 where
  TensorIrrepRep SU2 j1 j2 = TensorIrrepRepSU2 j1 j2
  TensorIrrepRep U1 j1 j2 = '[ '(Add j1 j2, 1) ]

-- | Tag every CG output sector with the same copy space.
type IrrepRepWithCopy
  :: forall (g :: Group) -> Type -> [(Irreps g, Multiplicity)] -> Reps g
type family IrrepRepWithCopy g copy reps where
  IrrepRepWithCopy U1 copy '[] = '[]
  IrrepRepWithCopy U1 copy ('(j, _) ': xs) =
    '(j, copy) ': IrrepRepWithCopy U1 copy xs
  IrrepRepWithCopy SU2 copy '[] = '[]
  IrrepRepWithCopy SU2 copy ('(j, _) ': xs) =
    '(j, copy) ': IrrepRepWithCopy SU2 copy xs

--------------------------------------------------------------------------------
-- Type-level Tensor: Coalesce ∘ TensorRaw (Distribute + leaf CG + scale)
--
-- Call sites use group-indexed 'Coalesce' / 'Tensor' / …. Workers stay
-- U1-/SU2-specialized: GHC rejects closed-TF equations with polymorphic @g@
-- when an argument kind mentions @Irreps g@ (@Irreps@ is a type family).
--------------------------------------------------------------------------------

type DualIrrep :: forall (g :: Group) -> Irreps g -> Irreps g
type family DualIrrep g p where
  DualIrrep U1 q = Negate q
  DualIrrep SU2 j = j

type DualRep :: forall (g :: Group) -> Reps g -> Reps g
type family DualRep g r where
  DualRep U1 '[] = '[]
  DualRep SU2 '[] = '[]
  DualRep U1 ('(i, copy) ': rs) = '(DualIrrep U1 i, copy) ': DualRep U1 rs
  DualRep SU2 ('(i, copy) ': rs) = '(DualIrrep SU2 i, copy) ': DualRep SU2 rs

-- | Uncoalesced CG branching (left × right, Append order).
type TensorRaw
  :: forall (g :: Group) -> Reps g -> Reps g -> Reps g
type family TensorRaw g r q where
  TensorRaw U1 '[] _ = '[]
  TensorRaw SU2 '[] _ = '[]
  TensorRaw U1 ('(i, copy) ': rs) q =
    Append (TensorOne U1 '(i, copy) q) (TensorRaw U1 rs q)
  TensorRaw SU2 ('(i, copy) ': rs) q =
    Append (TensorOne SU2 '(i, copy) q) (TensorRaw SU2 rs q)

type TensorOne
  :: forall (g :: Group) -> MultipleIrreps g -> Reps g -> Reps g
type family TensorOne g x q where
  TensorOne U1 _ '[] = '[]
  TensorOne U1 ('(i, Atom m)) ('(j, Atom n) ': qs) =
    Append
      (IrrepRepWithCopy U1 (Prod m n) (TensorIrrepRep U1 i j))
      (TensorOne U1 ('(i, Atom m)) qs)
  TensorOne SU2 _ '[] = '[]
  TensorOne SU2 ('(i, Atom m)) ('(j, Atom n) ': qs) =
    Append
      (IrrepRepWithCopy SU2 (Prod m n) (TensorIrrepRep SU2 i j))
      (TensorOne SU2 ('(i, Atom m)) qs)

type Coalesce :: forall (g :: Group) -> Reps g -> Reps g
type family Coalesce g r where
  Coalesce U1 r = CoalesceU1 r
  Coalesce SU2 r = CoalesceSU2 r

type family CoalesceU1 (r :: Reps U1) :: Reps U1 where
  CoalesceU1 '[] = '[]
  CoalesceU1 ('(j, copy) ': rest) = InsertSectorU1 j copy (CoalesceU1 rest)

type family CoalesceSU2 (r :: Reps SU2) :: Reps SU2 where
  CoalesceSU2 '[] = '[]
  CoalesceSU2 ('(j, copy) ': rest) = InsertSectorSU2 j copy (CoalesceSU2 rest)

type family InsertSectorU1 j copy r where
  InsertSectorU1 j copy '[] = '[ '(j, copy)]
  InsertSectorU1 j copy ('(j2, copy2) ': rest) =
    InsertSectorZMult (CmpZ j j2) j copy j2 copy2 rest

type family InsertSectorSU2 j copy r where
  InsertSectorSU2 j copy '[] = '[ '(j, copy)]
  InsertSectorSU2 j copy ('(j2, copy2) ': rest) =
    InsertSectorNatMult (CmpNat j j2) j copy j2 copy2 rest

-- | Same-irrep merge: atoms/products flatten to an 'Atom' of summed dimension.
type family InsertSectorNatMult o j copy j2 copy2 rest where
  InsertSectorNatMult 'EQ j (Atom m) _ (Atom n) rest =
    '(j, Atom (m + n)) ': rest
  InsertSectorNatMult 'EQ j (Prod m n) _ (Prod m2 n2) rest =
    '(j, Atom (m * n + m2 * n2)) ': rest
  InsertSectorNatMult 'EQ j copy _ _ rest = '(j, copy) ': rest
  InsertSectorNatMult 'LT j copy j2 copy2 rest =
    '(j, copy) ': '(j2, copy2) ': rest
  InsertSectorNatMult 'GT j copy j2 copy2 rest =
    '(j2, copy2) ': InsertSectorSU2 j copy rest

type family InsertSectorZMult o j copy j2 copy2 rest where
  InsertSectorZMult 'EQ j (Atom m) _ (Atom n) rest =
    '(j, Atom (m + n)) ': rest
  InsertSectorZMult 'EQ j (Prod m n) _ (Prod m2 n2) rest =
    '(j, Atom (m * n + m2 * n2)) ': rest
  InsertSectorZMult 'EQ j copy _ _ rest = '(j, copy) ': rest
  InsertSectorZMult 'LT j copy j2 copy2 rest =
    '(j, copy) ': '(j2, copy2) ': rest
  InsertSectorZMult 'GT j copy j2 copy2 rest =
    '(j2, copy2) ': InsertSectorU1 j copy rest

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

-- | Fused + coalesced Reps @r ⊗ q@.
type Tensor :: forall (g :: Group) -> Reps g -> Reps g -> Reps g
type family Tensor g r q where
  Tensor g r q = Coalesce g (TensorRaw g r q)

-- | Drop copy spaces to flat multiplicity ('KnownRep' / CG).
type ForgetCopyLabel
  :: forall (g :: Group) -> Reps g -> [(Irreps g, Multiplicity)]
type family ForgetCopyLabel g rs where
  ForgetCopyLabel U1 '[] = '[]
  ForgetCopyLabel U1 ('(j, copy) ': rs) =
    '(j, DimOf copy) ': ForgetCopyLabel U1 rs
  ForgetCopyLabel SU2 '[] = '[]
  ForgetCopyLabel SU2 ('(j, copy) ': rs) =
    '(j, DimOf copy) ': ForgetCopyLabel SU2 rs

type FilterNonTrivial :: forall (g :: Group) -> Reps g -> Reps g
type family FilterNonTrivial g r where
  FilterNonTrivial U1 '[] = '[]
  FilterNonTrivial U1 ('( 'Zero, copy) ': rs) =
    '( 'Zero, copy) ': FilterNonTrivial U1 rs
  FilterNonTrivial U1 ('(i, copy) ': rs) = FilterNonTrivial U1 rs
  FilterNonTrivial SU2 '[] = '[]
  FilterNonTrivial SU2 ('(0, copy) ': rs) =
    '(0, copy) ': FilterNonTrivial SU2 rs
  FilterNonTrivial SU2 ('(i, copy) ': rs) = FilterNonTrivial SU2 rs

-- | Hom space as trivial sector of @Dual r ⊗ q@.
type family (a :: Type) `Intertwiner` (b :: Type) :: Type where
  (Representation g r) `Intertwiner` (Representation g q) =
    HList (RepToVectors g (FilterNonTrivial g (Tensor g (DualRep g r) q)))

type Fuse g r q = HList (RepToVectors g (Tensor g r q))

type BraidedFuse g r q = HList (RepToVectors g (BraidReps g (Tensor g r q)))

type UnfusePair g x y =
  Sector g (Fst x) (Snd x) ⊗ Sector g (Fst y) (Snd y)

type UnfuseOne :: forall (g :: Group) -> MultipleIrreps g -> Reps g -> [Type]
type family UnfuseOne g x q where
  UnfuseOne U1 x '[] = '[]
  UnfuseOne SU2 x '[] = '[]
  UnfuseOne U1 x ('(j, lbl) ': qs) =
    UnfusePair U1 x '(j, lbl) ': UnfuseOne U1 x qs
  UnfuseOne SU2 x ('(j, lbl) ': qs) =
    UnfusePair SU2 x '(j, lbl) ': UnfuseOne SU2 x qs

type UnfuseRaw :: forall (g :: Group) -> Reps g -> Reps g -> [Type]
type family UnfuseRaw g r q where
  UnfuseRaw U1 '[] _ = '[]
  UnfuseRaw SU2 '[] _ = '[]
  UnfuseRaw U1 ('(i, lbl) ': rs) q =
    Append (UnfuseOne U1 '(i, lbl) q) (UnfuseRaw U1 rs q)
  UnfuseRaw SU2 ('(i, lbl) ': rs) q =
    Append (UnfuseOne SU2 '(i, lbl) q) (UnfuseRaw SU2 rs q)

-- | Term-level unfused @r ⊗ q@ payload.
type Unfuse g r q = HList (UnfuseRaw g r q)

type family Fst (p :: (k, l)) :: k where
  Fst '(a, _) = a

type family Snd (p :: (k, l)) :: l where
  Snd '(_, b) = b

--------------------------------------------------------------------------------
-- Direct-sum basis for sector HLists
--------------------------------------------------------------------------------

-- | Nested @Either@ basis of an HList of 'HasBasis' sectors.
type family RepBasis (xs :: [Type]) :: Type where
  RepBasis '[] = Void
  RepBasis (x ': xs) = Either (Basis x) (RepBasis xs)

instance AdditiveGroup (HList '[]) where
  zeroV = HNil
  HNil ^+^ HNil = HNil
  negateV HNil = HNil

instance
  ( AdditiveGroup x
  , AdditiveGroup (HList xs)
  ) =>
  AdditiveGroup (HList (x ': xs))
  where
  zeroV = zeroV :& zeroV
  (x :& xs) ^+^ (y :& ys) = (x ^+^ y) :& (xs ^+^ ys)
  negateV (x :& xs) = negateV x :& negateV xs

instance VectorSpace (HList '[]) where
  type Scalar (HList '[]) = Complex Double
  _ *^ v = v

instance
  ( VectorSpace x
  , Scalar x ~ Complex Double
  , VectorSpace (HList xs)
  , Scalar (HList xs) ~ Complex Double
  , AdditiveGroup (HList (x ': xs))
  ) =>
  VectorSpace (HList (x ': xs))
  where
  type Scalar (HList (x ': xs)) = Complex Double
  μ *^ (x :& xs) = (μ *^ x) :& (μ *^ xs)

instance HasBasis (HList '[]) where
  type Basis (HList '[]) = RepBasis '[]
  basisValue = absurd
  decompose HNil = []
  decompose' HNil = absurd

instance
  ( HasBasis x
  , Scalar x ~ Complex Double
  , AdditiveGroup x
  , HasBasis (HList xs)
  , Scalar (HList xs) ~ Complex Double
  , AdditiveGroup (HList xs)
  , Basis (HList xs) ~ RepBasis xs
  ) =>
  HasBasis (HList (x ': xs))
  where
  type Basis (HList (x ': xs)) = RepBasis (x ': xs)
  basisValue (Left b) = basisValue b :& zeroV
  basisValue (Right b) = zeroV :& basisValue b
  decompose (x :& xs) =
    map (first Left) (decompose x)
      ++ map (first Right) (decompose xs)
  decompose' (x :& xs) =
    either (decompose' x) (decompose' xs)

--------------------------------------------------------------------------------
-- Constructors / helpers
--------------------------------------------------------------------------------

stdBasisC :: forall k. KnownNat k => Int -> C k
stdBasisC i =
  let d = fromIntegral (natVal (Proxy @k)) :: Int
  in  fromList [ if j == i then 1 else 0 | j <- [0 .. d - 1] ]

oneC1 :: C 1
oneC1 = fromList [1]

-- | Pack multiplicity copies into an atom sector @C m ⊗ C d@.
packAtomIrrep
  :: forall m d. (KnownNat m, KnownNat d)
  => [C d]
  -> Atom m ⊗ C d
packAtomIrrep vs =
  sumV [ stdBasisC @m i ⊗ v | (i, v) <- zip [0 ..] vs ]

asSector1
  :: forall g j.
     ( KnownNat (IrrepDim g j)
     )
  => Irrep g j
  -> Sector g j (Atom 1)
asSector1 (Irrep c) = oneC1 ⊗ c

tensorSectors
  :: forall g a m b n.
     ( KnownNat m
     , KnownNat n
     , KnownNat (IrrepDim g a)
     , KnownNat (IrrepDim g b)
     , UnfuseRaw g '[ '(a, Atom m)] '[ '(b, Atom n)]
         ~ '[UnfusePair g '(a, Atom m) '(b, Atom n)]
     )
  => Sector g a (Atom m)
  -> Sector g b (Atom n)
  -> Unfuse g '[ '(a, Atom m)] '[ '(b, Atom n)]
tensorSectors ua vb = (ua ⊗ vb) :& HNil

swapUnfuse
  :: forall g a m b n.
     ( KnownNat m
     , KnownNat n
     , KnownNat (IrrepDim g a)
     , KnownNat (IrrepDim g b)
     , UnfuseRaw g '[ '(a, Atom m)] '[ '(b, Atom n)]
         ~ '[UnfusePair g '(a, Atom m) '(b, Atom n)]
     , UnfuseRaw g '[ '(b, Atom n)] '[ '(a, Atom m)]
         ~ '[UnfusePair g '(b, Atom n) '(a, Atom m)]
     )
  => Unfuse g '[ '(a, Atom m)] '[ '(b, Atom n)]
  -> Unfuse g '[ '(b, Atom n)] '[ '(a, Atom m)]
swapUnfuse (t :& HNil) = (swapMap $ t) :& HNil

--------------------------------------------------------------------------------
-- fuse = recompose . f . decompose
--------------------------------------------------------------------------------

-- | Unpack flat fused buffer into typed fused sectors (CG output boundary).
class UnpackFusedFlat g (rs :: Reps g) where
  unpackFusedFlat :: VS.Vector (Complex Double) -> HList (RepToVectors g rs)

instance UnpackFusedFlat U1 '[] where
  unpackFusedFlat _ = HNil

instance UnpackFusedFlat SU2 '[] where
  unpackFusedFlat _ = HNil

instance
  ( KnownNat m
  , KnownNat (IrrepDim U1 j)
  , KnownNat (DimOf (Atom m))
  , KnownNat (DimOf (Atom m) * IrrepDim U1 j)
  , UnpackFusedFlat U1 rs
  , RepToVectors U1 ('(j, Atom m) ': rs)
      ~ (Sector U1 j (Atom m) ': RepToVectors U1 rs)
  ) =>
  UnpackFusedFlat U1 ('(j, Atom m) ': rs)
  where
  unpackFusedFlat flat =
    let d =
          fromIntegral (natVal (Proxy @(DimOf (Atom m))))
            * fromIntegral (natVal (Proxy @(IrrepDim U1 j)))
        (here, rest) = VS.splitAt d flat
    in  (unsafeFromArray here :: Sector U1 j (Atom m))
        :& unpackFusedFlat @U1 @rs rest

instance
  ( KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim U1 j)
  , KnownNat (DimOf (Prod m n))
  , KnownNat (DimOf (Prod m n) * IrrepDim U1 j)
  , UnpackFusedFlat U1 rs
  , RepToVectors U1 ('(j, Prod m n) ': rs)
      ~ (Sector U1 j (Prod m n) ': RepToVectors U1 rs)
  ) =>
  UnpackFusedFlat U1 ('(j, Prod m n) ': rs)
  where
  unpackFusedFlat flat =
    let d =
          fromIntegral (natVal (Proxy @(DimOf (Prod m n))))
            * fromIntegral (natVal (Proxy @(IrrepDim U1 j)))
        (here, rest) = VS.splitAt d flat
    in  (unsafeFromArray here :: Sector U1 j (Prod m n))
        :& unpackFusedFlat @U1 @rs rest

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim SU2 j)
  , KnownNat (DimOf (Atom m))
  , KnownNat (DimOf (Atom m) * IrrepDim SU2 j)
  , UnpackFusedFlat SU2 rs
  , RepToVectors SU2 ('(j, Atom m) ': rs)
      ~ (Sector SU2 j (Atom m) ': RepToVectors SU2 rs)
  ) =>
  UnpackFusedFlat SU2 ('(j, Atom m) ': rs)
  where
  unpackFusedFlat flat =
    let d =
          fromIntegral (natVal (Proxy @(DimOf (Atom m))))
            * fromIntegral (natVal (Proxy @(IrrepDim SU2 j)))
        (here, rest) = VS.splitAt d flat
    in  (unsafeFromArray here :: Sector SU2 j (Atom m))
        :& unpackFusedFlat @SU2 @rs rest

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim SU2 j)
  , KnownNat (DimOf (Prod m n))
  , KnownNat (DimOf (Prod m n) * IrrepDim SU2 j)
  , UnpackFusedFlat SU2 rs
  , RepToVectors SU2 ('(j, Prod m n) ': rs)
      ~ (Sector SU2 j (Prod m n) ': RepToVectors SU2 rs)
  ) =>
  UnpackFusedFlat SU2 ('(j, Prod m n) ': rs)
  where
  unpackFusedFlat flat =
    let d =
          fromIntegral (natVal (Proxy @(DimOf (Prod m n))))
            * fromIntegral (natVal (Proxy @(IrrepDim SU2 j)))
        (here, rest) = VS.splitAt d flat
    in  (unsafeFromArray here :: Sector SU2 j (Prod m n))
        :& unpackFusedFlat @SU2 @rs rest

-- | Fusion intertwiner @Φ : unfused → fused@ via @recompose . f . decompose@.
-- Leaf CG input is @toArray@ of the single unfused pair tensor.
class CanFuse g r q where
  fuse :: Unfuse g r q -> Fuse g r q

instance
  ( KnownNat a
  , KnownNat b
  , KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim SU2 a)
  , KnownNat (IrrepDim SU2 b)
  , KnownRep SG.SU2 (ForgetCopyLabel SU2 '[ '(a, Atom m)])
  , KnownRep SG.SU2 (ForgetCopyLabel SU2 '[ '(b, Atom n)])
  , UnpackFusedFlat SU2 (Tensor SU2 '[ '(a, Atom m)] '[ '(b, Atom n)])
  , UnfuseRaw SU2 '[ '(a, Atom m)] '[ '(b, Atom n)]
      ~ '[UnfusePair SU2 '(a, Atom m) '(b, Atom n)]
  , DimensionAware (UnfusePair SU2 '(a, Atom m) '(b, Atom n))
  , HasBasis (Unfuse SU2 '[ '(a, Atom m)] '[ '(b, Atom n)])
  , HasBasis (Fuse SU2 '[ '(a, Atom m)] '[ '(b, Atom n)])
  , Scalar (Unfuse SU2 '[ '(a, Atom m)] '[ '(b, Atom n)]) ~ Complex Double
  , Scalar (Fuse SU2 '[ '(a, Atom m)] '[ '(b, Atom n)]) ~ Complex Double
  ) =>
  CanFuse SU2 '[ '(a, Atom m)] '[ '(b, Atom n)]
  where
  fuse =
    recompose @(Fuse SU2 '[ '(a, Atom m)] '[ '(b, Atom n)])
      . f
      . decompose @(Unfuse SU2 '[ '(a, Atom m)] '[ '(b, Atom n)])
    where
      flatFuse (t :& HNil) =
        unpackFusedFlat @SU2 @(Tensor SU2 '[ '(a, Atom m)] '[ '(b, Atom n)]) $
          fuseSU2Flat
            (repSing @SG.SU2 @(ForgetCopyLabel SU2 '[ '(a, Atom m)]))
            (repSing @SG.SU2 @(ForgetCopyLabel SU2 '[ '(b, Atom n)]))
            (toArray t)
      f =
        concatMap
          ( \(b, c) ->
              [ (b', c * coeff)
              | (b', coeff) <-
                  decompose @(Fuse SU2 '[ '(a, Atom m)] '[ '(b, Atom n)])
                    (flatFuse (basisValue @(Unfuse SU2 '[ '(a, Atom m)] '[ '(b, Atom n)]) b))
              ]
          )

instance
  ( KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim U1 a)
  , KnownNat (IrrepDim U1 b)
  , SingI a
  , SingI b
  , KnownRep SG.U1 (ForgetCopyLabel U1 '[ '(a, Atom m)])
  , KnownRep SG.U1 (ForgetCopyLabel U1 '[ '(b, Atom n)])
  , UnpackFusedFlat U1 (Tensor U1 '[ '(a, Atom m)] '[ '(b, Atom n)])
  , UnfuseRaw U1 '[ '(a, Atom m)] '[ '(b, Atom n)]
      ~ '[UnfusePair U1 '(a, Atom m) '(b, Atom n)]
  , DimensionAware (UnfusePair U1 '(a, Atom m) '(b, Atom n))
  , HasBasis (Unfuse U1 '[ '(a, Atom m)] '[ '(b, Atom n)])
  , HasBasis (Fuse U1 '[ '(a, Atom m)] '[ '(b, Atom n)])
  , Scalar (Unfuse U1 '[ '(a, Atom m)] '[ '(b, Atom n)]) ~ Complex Double
  , Scalar (Fuse U1 '[ '(a, Atom m)] '[ '(b, Atom n)]) ~ Complex Double
  ) =>
  CanFuse U1 '[ '(a, Atom m)] '[ '(b, Atom n)]
  where
  fuse =
    recompose @(Fuse U1 '[ '(a, Atom m)] '[ '(b, Atom n)])
      . f
      . decompose @(Unfuse U1 '[ '(a, Atom m)] '[ '(b, Atom n)])
    where
      flatFuse (t :& HNil) =
        unpackFusedFlat @U1 @(Tensor U1 '[ '(a, Atom m)] '[ '(b, Atom n)]) $
          fuseU1Flat
            (repSing @SG.U1 @(ForgetCopyLabel U1 '[ '(a, Atom m)]))
            (repSing @SG.U1 @(ForgetCopyLabel U1 '[ '(b, Atom n)]))
            (toArray t)
      f =
        concatMap
          ( \(b, c) ->
              [ (b', c * coeff)
              | (b', coeff) <-
                  decompose @(Fuse U1 '[ '(a, Atom m)] '[ '(b, Atom n)])
                    (flatFuse (basisValue @(Unfuse U1 '[ '(a, Atom m)] '[ '(b, Atom n)]) b))
              ]
          )

--------------------------------------------------------------------------------
-- rmove
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
  :: forall j1 j2 j lbl.
     ( KnownNat j1
     , KnownNat j2
     , KnownNat j
     , KnownNat (IrrepDim SU2 j)
     , VectorSpace (Sector SU2 j lbl)
     , Scalar (Sector SU2 j lbl) ~ Complex Double
     )
  => Sector SU2 j lbl
  -> Sector SU2 j lbl
rPhaseSector = (rPhaseScalar @j1 @j2 @j *^)

-- | Categorical swap of copy factors @C m ⊗ C n@ (irrep leg unchanged).
swapCopyProductSector
  :: forall m n d.
     ( KnownNat m
     , KnownNat n
     , KnownNat d
     , LSpace (C m)
     , LSpace (C n)
     , LSpace (C d)
     , LSpace (C m ⊗ C n)
     , LSpace (C n ⊗ C m)
     , LSpace (C m ⊗ C n ⊗ C d)
     , LSpace (C n ⊗ C m ⊗ C d)
     , TensorSpace (C m ⊗ C n ⊗ C d)
     , Scalar (C m) ~ Complex Double
     , Scalar (C n) ~ Complex Double
     , Scalar (C d) ~ Complex Double
     )
  => (C m ⊗ C n) ⊗ C d
  -> (C n ⊗ C m) ⊗ C d
swapCopyProductSector sec = (swapMap ⊗^ id) $ sec

-- | Braiding fused sectors: R-phase (SU2, via @a@/@b@) then braid copy.
class CanRmove g (a :: Irreps g) (b :: Irreps g) (rs :: Reps g) where
  rmoveSectors
    :: HList (RepToVectors g rs)
    -> HList (RepToVectors g (BraidReps g rs))

instance CanRmove U1 a b '[] where
  rmoveSectors HNil = HNil

instance CanRmove SU2 a b '[] where
  rmoveSectors HNil = HNil

instance
  ( CanRmove U1 a b rs
  , BraidCopy (Atom m) ~ Atom m
  ) =>
  CanRmove U1 a b ('(j, Atom m) ': rs)
  where
  rmoveSectors (sec :& rest) = sec :& rmoveSectors @U1 @a @b @rs rest

instance
  ( CanRmove SU2 a b rs
  , KnownNat a
  , KnownNat b
  , KnownNat m
  , KnownNat j
  , BraidCopy (Atom m) ~ Atom m
  ) =>
  CanRmove SU2 a b ('(j, Atom m) ': rs)
  where
  rmoveSectors (sec :& rest) =
    rPhaseSector @a @b @j @(Atom m) sec
      :& rmoveSectors @SU2 @a @b @rs rest

instance
  ( CanRmove U1 a b rs
  , KnownNat m
  , KnownNat n
  , BraidCopy (Prod m n) ~ Prod n m
  ) =>
  CanRmove U1 a b ('(j, Prod m n) ': rs)
  where
  rmoveSectors (sec :& rest) =
    swapCopyProductSector @m @n @(IrrepDim U1 j) sec
      :& rmoveSectors @U1 @a @b @rs rest

instance
  ( CanRmove SU2 a b rs
  , KnownNat a
  , KnownNat b
  , KnownNat m
  , KnownNat n
  , KnownNat j
  , BraidCopy (Prod m n) ~ Prod n m
  ) =>
  CanRmove SU2 a b ('(j, Prod m n) ': rs)
  where
  rmoveSectors (sec :& rest) =
    swapCopyProductSector @m @n @(IrrepDim SU2 j)
      (rPhaseSector @a @b @j @(Prod m n) sec)
      :& rmoveSectors @SU2 @a @b @rs rest

-- | Leaf braiding @r ⊗ q → q ⊗ r@ on a fused pair.
rmove
  :: forall g a m b n.
     ( CanRmove g a b (Tensor g '[ '(a, Atom m)] '[ '(b, Atom n)])
     )
  => Fuse g '[ '(a, Atom m)] '[ '(b, Atom n)]
  -> BraidedFuse g '[ '(a, Atom m)] '[ '(b, Atom n)]
rmove =
  rmoveSectors @g @a @b @(Tensor g '[ '(a, Atom m)] '[ '(b, Atom n)])
