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
import Math.LinearMap.Asserted (getLinearFunction, linearFunction)
import qualified Math.LinearMap.Category as LM (Tensor (..))
import Math.VectorSpace.DimensionAware
  ( DimensionAware (..)
  , Dimensional (..)
  , StaticDimension
  , toArray
  , unsafeFromArray
  )
import Numeric.LinearAlgebra.Static (C, Sized (fromList))
import Prelude hiding (id, (.), ($))
import qualified Symmetry.Group as SG
import Symmetry.CG.FSymbol
  ( BuildEyeHomG
  , PackSchur
  , fSymbolHomSU2
  , fSymbolHomSU2Inv
  , fSymbolHomU1
  , fSymbolHomU1Inv
  )
import Symmetry.CG.SU2 (fuseSU2Flat)
import Symmetry.CG.U1 (fuseU1Flat)
import Symmetry.ChargeEq ()
import Symmetry.FunctorExperiment
  ( ApplyIntertwinerG
  , CollectCompiledGo
  , IntertwinerG (..)
  , RepListG
  , RepLookup
  , ToCG (..)
  , intertwinerLinearG
  )
import Symmetry.Group (IntertwinerHom, RepDimG)
import Symmetry.HomBlock (HasHomBlock)
import Symmetry.RepSingleton (KnownRep (..))
import qualified Symmetry.Tensor as ST
import Symmetry.Utils
  ( Add
  , Append
  , HList (..)
  , Negate
  , Z (..)
  )
import TensorNetwork.Categorical ((⊗^), runit, swapMap)
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

-- | Monoidal unit object (trivial irrep, multiplicity 1).
type Trivial :: forall (g :: Group) -> Irreps g
type family Trivial g where
  Trivial U1 = 'Zero
  Trivial SU2 = 0

type Unit (g :: Group) = '[ '(Trivial g, Atom 1)]

-- | Leaf spine @'[ '(j, Atom m)]@.
type Leaf (g :: Group) (j :: Irreps g) (m :: Nat) = '[ '(j, Atom m)]

-- | Flat multiplicity rep for CG / F-symbol plumbing.
type Flat g (rs :: Reps g) = ForgetCopyLabel g rs

type FusedLeft
  (g :: Group) (a :: Irreps g) (ma :: Nat) (b :: Irreps g) (mb :: Nat)
  (c :: Irreps g) (mc :: Nat) =
  Tensor g
    (FlattenCopies g (Tensor g (Leaf g a ma) (Leaf g b mb)))
    (Leaf g c mc)

type FusedRight
  (g :: Group) (a :: Irreps g) (ma :: Nat) (b :: Irreps g) (mb :: Nat)
  (c :: Irreps g) (mc :: Nat) =
  Tensor g
    (Leaf g a ma)
    (FlattenCopies g (Tensor g (Leaf g b mb) (Leaf g c mc)))

-- | Inner @(r ⊗ q)@ before attaching the third leaf in left parenthesization.
type MidFuseLeft
  (g :: Group) (a :: Irreps g) (ma :: Nat) (b :: Irreps g) (mb :: Nat) =
  FlattenCopies g (Tensor g (Leaf g a ma) (Leaf g b mb))

-- | Replace copy spaces by @Atom (DimOf copy)@ so outer 'TensorOne' (Atom×Atom)
-- can fire. Flat CG / F-symbol see the same 'ForgetCopyLabel' multiplicities.
type FlattenCopies :: forall (g :: Group) -> Reps g -> Reps g
type family FlattenCopies g rs where
  FlattenCopies U1 '[] = '[]
  FlattenCopies U1 ('(j, copy) ': rs) =
    '(j, Atom (DimOf copy)) ': FlattenCopies U1 rs
  FlattenCopies SU2 '[] = '[]
  FlattenCopies SU2 ('(j, copy) ': rs) =
    '(j, Atom (DimOf copy)) ': FlattenCopies SU2 rs

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

-- | Fuse @((r ⊗ q) ⊗ s)@ from three U(1) atomic sectors (left parenthesization).
fuseFusedLeftU1
  :: forall a ma b mb c mc j.
     ( KnownNat ma
     , KnownNat mb
     , KnownNat mc
     , j ~ Add a b
     , KnownNat (IrrepDim U1 a)
     , KnownNat (IrrepDim U1 b)
     , KnownNat (IrrepDim U1 c)
     , KnownNat (ma * mb)
     , SingI a
     , SingI b
     , SingI c
     , CanFuse U1 (Leaf U1 a ma) (Leaf U1 b mb)
     , KnownRep SG.U1 (ForgetCopyLabel U1 (MidFuseLeft U1 a ma b mb))
     , KnownRep SG.U1 (ForgetCopyLabel U1 (Leaf U1 c mc))
     , UnpackFusedFlat U1 (FusedLeft U1 a ma b mb c mc)
     , MidFuseLeft U1 a ma b mb ~ '[ '(j, Atom (ma * mb))]
     , DimensionAware (Sector U1 j (Atom (ma * mb)) ⊗ Sector U1 c (Atom mc))
     , (ma * mb) `Dimensional` Sector U1 j (Atom (ma * mb))
     , KnownNat (DimOf (Atom (ma * mb)) * IrrepDim U1 j)
     )
  => Sector U1 a (Atom ma)
  -> Sector U1 b (Atom mb)
  -> Sector U1 c (Atom mc)
  -> FuseSpine U1 (FusedLeft U1 a ma b mb c mc)
fuseFusedLeftU1 sa sb sc =
  unpackFusedFlat @U1 @(FusedLeft U1 a ma b mb c mc) $
    fuseU1Flat
      (repSing @SG.U1 @(ForgetCopyLabel U1 (MidFuseLeft U1 a ma b mb)))
      (repSing @SG.U1 @(ForgetCopyLabel U1 (Leaf U1 c mc)))
      (toArray (sectorFlat ⊗ sc))
  where
    (sectorRq :& HNil) =
      fuse @U1 @(Leaf U1 a ma) @(Leaf U1 b mb) (tensorSectors @U1 @a @ma @b @mb sa sb)
    sectorFlat :: Sector U1 j (Atom (ma * mb))
    sectorFlat = unsafeFromArray (toArray sectorRq :: VS.Vector (Complex Double))

-- | Fuse @((r ⊗ q) ⊗ s)@ for @j=0@ SU(2) atoms (left parenthesization).
fuseFusedLeftSU2
  :: forall c mc.
     ( KnownNat mc
     , KnownNat c
     , KnownNat (IrrepDim SU2 c)
     , CanFuse SU2 (Leaf SU2 0 1) (Leaf SU2 0 1)
     , KnownRep SG.SU2 (ForgetCopyLabel SU2 (MidFuseLeft SU2 0 1 0 1))
     , KnownRep SG.SU2 (ForgetCopyLabel SU2 (Leaf SU2 c mc))
     , UnpackFusedFlat SU2 (FusedLeft SU2 0 1 0 1 c mc)
     , MidFuseLeft SU2 0 1 0 1 ~ '[ '(0, Atom 1)]
     , DimensionAware (Sector SU2 0 (Atom 1) ⊗ Sector SU2 c (Atom mc))
     , 1 `Dimensional` Sector SU2 0 (Atom 1)
     )
  => Sector SU2 c (Atom mc)
  -> FuseSpine SU2 (FusedLeft SU2 0 1 0 1 c mc)
fuseFusedLeftSU2 sc =
  unpackFusedFlat @SU2 @(FusedLeft SU2 0 1 0 1 c mc) $
    fuseSU2Flat
      (repSing @SG.SU2 @(ForgetCopyLabel SU2 (MidFuseLeft SU2 0 1 0 1)))
      (repSing @SG.SU2 @(ForgetCopyLabel SU2 (Leaf SU2 c mc)))
      (toArray (sectorFlat ⊗ sc))
  where
    sa = asSector1 (Irrep (fromList [1]) :: Irrep SU2 0)
    sb = asSector1 (Irrep (fromList [1]) :: Irrep SU2 0)
    (sectorRq :& HNil) =
      fuse @SU2 @(Leaf SU2 0 1) @(Leaf SU2 0 1) (tensorSectors @SU2 @0 @1 @0 @1 sa sb)
    sectorFlat :: Sector SU2 0 (Atom 1)
    sectorFlat = unsafeFromArray (toArray sectorRq :: VS.Vector (Complex Double))

--------------------------------------------------------------------------------
-- rmove
--------------------------------------------------------------------------------


rPhaseSector
  :: forall j1 j2 j lbl.
     ( KnownNat j1
     , KnownNat j2
     , KnownNat j
     , VectorSpace (Sector SU2 j lbl)
     , Scalar (Sector SU2 j lbl) ~ Complex Double
     )
  => Sector SU2 j lbl -> Sector SU2 j lbl
rPhaseSector = ((((-1) ^ ((tj1 + tj2 - tj) `div` 2)) :+ 0) *^) where

  tj1 = fromIntegral (natVal (Proxy @j1)) :: Int
  tj2 = fromIntegral (natVal (Proxy @j2))
  tj = fromIntegral (natVal (Proxy @j))

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


--------------------------------------------------------------------------------
-- Fused unitors (leaf): I ⊗ X ≅ X ≅ X ⊗ I
--------------------------------------------------------------------------------

-- | @(C m ⊗ C 1) ⊗ C d → C m ⊗ C d@.
runitCopySector
  :: forall m d.
     ( KnownNat m
     , KnownNat d
     , LSpace (C m)
     , LSpace (C 1)
     , LSpace (C d)
     , LSpace (C m ⊗ C 1)
     , LSpace (C m ⊗ C d)
     , LSpace (C m ⊗ C 1 ⊗ C d)
     , TensorSpace (C m ⊗ C 1 ⊗ C d)
     , TensorSpace (C m ⊗ C d)
     , Scalar (C m) ~ Complex Double
     , Scalar (C d) ~ Complex Double
     )
  => (C m ⊗ C 1) ⊗ C d
  -> C m ⊗ C d
runitCopySector sec = (runit @(C m) ⊗^ id) $ sec

-- | @(C 1 ⊗ C m) ⊗ C d → C m ⊗ C d@ (@swap@ then right unitor).
lunitCopySector
  :: forall m d.
     ( KnownNat m
     , KnownNat d
     , LSpace (C m)
     , LSpace (C 1)
     , LSpace (C d)
     , LSpace (C m ⊗ C 1)
     , LSpace (C 1 ⊗ C m)
     , LSpace (C m ⊗ C d)
     , LSpace (C m ⊗ C 1 ⊗ C d)
     , LSpace (C 1 ⊗ C m ⊗ C d)
     , TensorSpace (C m ⊗ C 1 ⊗ C d)
     , TensorSpace (C 1 ⊗ C m ⊗ C d)
     , TensorSpace (C m ⊗ C d)
     , Scalar (C m) ~ Complex Double
     , Scalar (C d) ~ Complex Double
     )
  => (C 1 ⊗ C m) ⊗ C d
  -> C m ⊗ C d
lunitCopySector sec =
  runitCopySector @m @d $ (swapMap ⊗^ id) $ sec

introRight1 :: forall m. (KnownNat m, LSpace (C m), Scalar (C m) ~ Complex Double)
  => C m +> (C m ⊗ C 1)
introRight1 = arr (linearFunction (\c -> c ⊗ oneC1))

introLeft1 :: forall m. (KnownNat m, LSpace (C m), Scalar (C m) ~ Complex Double)
  => C m +> (C 1 ⊗ C m)
introLeft1 = arr (linearFunction (\c -> oneC1 ⊗ c))

-- | @C m ⊗ C d → (C m ⊗ C 1) ⊗ C d@.
runitCopySectorInv
  :: forall m d.
     ( KnownNat m
     , KnownNat d
     , LSpace (C m)
     , LSpace (C 1)
     , LSpace (C d)
     , LSpace (C m ⊗ C 1)
     , LSpace (C m ⊗ C d)
     , LSpace (C m ⊗ C 1 ⊗ C d)
     , TensorSpace (C m ⊗ C d)
     , TensorSpace (C m ⊗ C 1 ⊗ C d)
     , Scalar (C m) ~ Complex Double
     , Scalar (C d) ~ Complex Double
     )
  => C m ⊗ C d
  -> (C m ⊗ C 1) ⊗ C d
runitCopySectorInv sec = (introRight1 @m ⊗^ id) $ sec

-- | @C m ⊗ C d → (C 1 ⊗ C m) ⊗ C d@.
lunitCopySectorInv
  :: forall m d.
     ( KnownNat m
     , KnownNat d
     , LSpace (C m)
     , LSpace (C 1)
     , LSpace (C d)
     , LSpace (C 1 ⊗ C m)
     , LSpace (C m ⊗ C d)
     , LSpace (C 1 ⊗ C m ⊗ C d)
     , TensorSpace (C m ⊗ C d)
     , TensorSpace (C 1 ⊗ C m ⊗ C d)
     , Scalar (C m) ~ Complex Double
     , Scalar (C d) ~ Complex Double
     )
  => C m ⊗ C d
  -> (C 1 ⊗ C m) ⊗ C d
lunitCopySectorInv sec = (introLeft1 @m ⊗^ id) $ sec

-- | Left fused unitor @λ : I ⊗ X → X@ (leaf).
lunitFuse
  :: forall g j m.
     ( Tensor g (Unit g) '[ '(j, Atom m)] ~ '[ '(j, Prod 1 m)]
     , RepToVectors g '[ '(j, Prod 1 m)] ~ '[Sector g j (Prod 1 m)]
     , RepToVectors g '[ '(j, Atom m)] ~ '[Sector g j (Atom m)]
     , KnownNat m
     , KnownNat (IrrepDim g j)
     , LSpace (C m)
     , LSpace (C 1)
     , LSpace (C (IrrepDim g j))
     , LSpace (C m ⊗ C 1)
     , LSpace (C 1 ⊗ C m)
     , LSpace (C m ⊗ C (IrrepDim g j))
     , LSpace (C m ⊗ C 1 ⊗ C (IrrepDim g j))
     , LSpace (C 1 ⊗ C m ⊗ C (IrrepDim g j))
     , TensorSpace (C m ⊗ C 1 ⊗ C (IrrepDim g j))
     , TensorSpace (C 1 ⊗ C m ⊗ C (IrrepDim g j))
     , TensorSpace (C m ⊗ C (IrrepDim g j))
     , Scalar (C m) ~ Complex Double
     , Scalar (C (IrrepDim g j)) ~ Complex Double
     )
  => Fuse g (Unit g) '[ '(j, Atom m)]
  -> HList (RepToVectors g '[ '(j, Atom m)])
lunitFuse (sec :& HNil) =
  lunitCopySector @m @(IrrepDim g j) sec :& HNil

-- | Right fused unitor @ρ : X ⊗ I → X@ (leaf).
runitFuse
  :: forall g j m.
     ( Tensor g '[ '(j, Atom m)] (Unit g) ~ '[ '(j, Prod m 1)]
     , RepToVectors g '[ '(j, Prod m 1)] ~ '[Sector g j (Prod m 1)]
     , RepToVectors g '[ '(j, Atom m)] ~ '[Sector g j (Atom m)]
     , KnownNat m
     , KnownNat (IrrepDim g j)
     , LSpace (C m)
     , LSpace (C 1)
     , LSpace (C (IrrepDim g j))
     , LSpace (C m ⊗ C 1)
     , LSpace (C m ⊗ C (IrrepDim g j))
     , LSpace (C m ⊗ C 1 ⊗ C (IrrepDim g j))
     , TensorSpace (C m ⊗ C 1 ⊗ C (IrrepDim g j))
     , TensorSpace (C m ⊗ C (IrrepDim g j))
     , Scalar (C m) ~ Complex Double
     , Scalar (C (IrrepDim g j)) ~ Complex Double
     )
  => Fuse g '[ '(j, Atom m)] (Unit g)
  -> HList (RepToVectors g '[ '(j, Atom m)])
runitFuse (sec :& HNil) =
  runitCopySector @m @(IrrepDim g j) sec :& HNil

lunitFuseInv
  :: forall g j m.
     ( Tensor g (Unit g) '[ '(j, Atom m)] ~ '[ '(j, Prod 1 m)]
     , RepToVectors g '[ '(j, Prod 1 m)] ~ '[Sector g j (Prod 1 m)]
     , RepToVectors g '[ '(j, Atom m)] ~ '[Sector g j (Atom m)]
     , KnownNat m
     , KnownNat (IrrepDim g j)
     , LSpace (C m)
     , LSpace (C 1)
     , LSpace (C (IrrepDim g j))
     , LSpace (C 1 ⊗ C m)
     , LSpace (C m ⊗ C (IrrepDim g j))
     , LSpace (C 1 ⊗ C m ⊗ C (IrrepDim g j))
     , TensorSpace (C m ⊗ C (IrrepDim g j))
     , TensorSpace (C 1 ⊗ C m ⊗ C (IrrepDim g j))
     , Scalar (C m) ~ Complex Double
     , Scalar (C (IrrepDim g j)) ~ Complex Double
     )
  => HList (RepToVectors g '[ '(j, Atom m)])
  -> Fuse g (Unit g) '[ '(j, Atom m)]
lunitFuseInv (sec :& HNil) =
  lunitCopySectorInv @m @(IrrepDim g j) sec :& HNil

runitFuseInv
  :: forall g j m.
     ( Tensor g '[ '(j, Atom m)] (Unit g) ~ '[ '(j, Prod m 1)]
     , RepToVectors g '[ '(j, Prod m 1)] ~ '[Sector g j (Prod m 1)]
     , RepToVectors g '[ '(j, Atom m)] ~ '[Sector g j (Atom m)]
     , KnownNat m
     , KnownNat (IrrepDim g j)
     , LSpace (C m)
     , LSpace (C 1)
     , LSpace (C (IrrepDim g j))
     , LSpace (C m ⊗ C 1)
     , LSpace (C m ⊗ C (IrrepDim g j))
     , LSpace (C m ⊗ C 1 ⊗ C (IrrepDim g j))
     , TensorSpace (C m ⊗ C (IrrepDim g j))
     , TensorSpace (C m ⊗ C 1 ⊗ C (IrrepDim g j))
     , Scalar (C m) ~ Complex Double
     , Scalar (C (IrrepDim g j)) ~ Complex Double
     )
  => HList (RepToVectors g '[ '(j, Atom m)])
  -> Fuse g '[ '(j, Atom m)] (Unit g)
runitFuseInv (sec :& HNil) =
  runitCopySectorInv @m @(IrrepDim g j) sec :& HNil

--------------------------------------------------------------------------------
-- F-move (leaf): ((r ⊗ q) ⊗ s) → (r ⊗ (q ⊗ s))
--------------------------------------------------------------------------------

class FusedToArray (xs :: [Type]) where
  fusedToArray :: HList xs -> VS.Vector (Complex Double)

instance FusedToArray '[] where
  fusedToArray HNil = VS.empty

instance
  ( KnownNat n
  , n `Dimensional` x
  , Scalar x ~ Complex Double
  , FusedToArray xs
  ) =>
  FusedToArray (x ': xs)
  where
  fusedToArray (x :& xs) =
    VS.concat [toArray x, fusedToArray xs]

type STLeft g r q s = ST.Tensor g (ST.Tensor g r q) s
type STRight g r q s = ST.Tensor g r (ST.Tensor g q s)

applyFlatInter
  :: forall g r q.
     ( RepLookup g
     , HasHomBlock g
     , CollectCompiledGo g
     , KnownRep g r
     , KnownRep g q
     , RepListG g r
     , RepListG g q
     , ApplyIntertwinerG g r q
     , KnownNat (RepDimG g r)
     , KnownNat (RepDimG g q)
     )
  => IntertwinerG g r q
  -> VS.Vector (Complex Double)
  -> VS.Vector (Complex Double)
applyFlatInter mor vin =
  case getLinearFunction (intertwinerLinearG mor) (ToCG (unsafeFromArray vin)) of
    ToCG out -> toArray out

type FuseSpine g (rs :: Reps g) = HList (RepToVectors g rs)

type FusedLeftSpine
  g a ma b mb c mc = RepToVectors g (FusedLeft g a ma b mb c mc)

type FusedRightSpine
  g a ma b mb c mc = RepToVectors g (FusedRight g a ma b mb c mc)

class CanFmove g (a :: Irreps g) (ma :: Nat) (b :: Irreps g) (mb :: Nat) (c :: Irreps g) (mc :: Nat) where
  fmove
    :: FuseSpine g (FusedLeft g a ma b mb c mc)
    -> FuseSpine g (FusedRight g a ma b mb c mc)
  fmoveInv
    :: FuseSpine g (FusedRight g a ma b mb c mc)
    -> FuseSpine g (FusedLeft g a ma b mb c mc)

instance
  ( KnownNat ma
  , KnownNat mb
  , KnownNat mc
  , SingI a
  , SingI b
  , SingI c
  , r ~ Flat U1 (Leaf U1 a ma)
  , q ~ Flat U1 (Leaf U1 b mb)
  , s ~ Flat U1 (Leaf U1 c mc)
  , left ~ Flat U1 (FusedLeft U1 a ma b mb c mc)
  , right ~ Flat U1 (FusedRight U1 a ma b mb c mc)
  , stLeft ~ STLeft SG.U1 r q s
  , stRight ~ STRight SG.U1 r q s
  , KnownRep SG.U1 r
  , KnownRep SG.U1 q
  , KnownRep SG.U1 s
  , KnownRep SG.U1 (ST.Tensor SG.U1 r q)
  , KnownRep SG.U1 (ST.Tensor SG.U1 q s)
  , KnownRep SG.U1 stLeft
  , KnownRep SG.U1 stRight
  , UnpackFusedFlat U1 (FusedLeft U1 a ma b mb c mc)
  , UnpackFusedFlat U1 (FusedRight U1 a ma b mb c mc)
  , FusedToArray (FusedLeftSpine U1 a ma b mb c mc)
  , FusedToArray (FusedRightSpine U1 a ma b mb c mc)
  , BuildEyeHomG SG.U1 (IntertwinerHom SG.U1 stLeft stRight)
  , BuildEyeHomG SG.U1 (IntertwinerHom SG.U1 stRight stLeft)
  , Add (Add a b) c ~ Add a (Add b c)
  , (ma * mb) * mc ~ ma * (mb * mc)
  , RepListG SG.U1 stLeft
  , RepListG SG.U1 stRight
  , KnownNat (RepDimG SG.U1 stLeft)
  , KnownNat (RepDimG SG.U1 stRight)
  , RepDimG SG.U1 left ~ RepDimG SG.U1 stLeft
  , RepDimG SG.U1 right ~ RepDimG SG.U1 stRight
  , HasBasis (FuseSpine U1 (FusedLeft U1 a ma b mb c mc))
  , HasBasis (FuseSpine U1 (FusedRight U1 a ma b mb c mc))
  , Scalar (FuseSpine U1 (FusedLeft U1 a ma b mb c mc)) ~ Complex Double
  , Scalar (FuseSpine U1 (FusedRight U1 a ma b mb c mc)) ~ Complex Double
  ) =>
  CanFmove U1 a ma b mb c mc
  where
  fmove =
    recompose @(FuseSpine U1 (FusedRight U1 a ma b mb c mc))
      . f
      . decompose @(FuseSpine U1 (FusedLeft U1 a ma b mb c mc))
    where
      mor = fSymbolHomU1 (Proxy @r) (Proxy @q) (Proxy @s)
      flatF t =
        unpackFusedFlat @U1 @(FusedRight U1 a ma b mb c mc) $
          applyFlatInter @SG.U1 @stLeft @stRight mor (fusedToArray t)
      f =
        concatMap
          ( \(b0, c0) ->
              [ (b1, c0 * coeff)
              | (b1, coeff) <-
                  decompose @(FuseSpine U1 (FusedRight U1 a ma b mb c mc))
                    ( flatF
                        ( basisValue
                            @(FuseSpine U1 (FusedLeft U1 a ma b mb c mc))
                            b0
                        )
                    )
              ]
          )

  fmoveInv =
    recompose @(FuseSpine U1 (FusedLeft U1 a ma b mb c mc))
      . f
      . decompose @(FuseSpine U1 (FusedRight U1 a ma b mb c mc))
    where
      mor = fSymbolHomU1Inv (Proxy @r) (Proxy @q) (Proxy @s)
      flatF t =
        unpackFusedFlat @U1 @(FusedLeft U1 a ma b mb c mc) $
          applyFlatInter @SG.U1 @stRight @stLeft mor (fusedToArray t)
      f =
        concatMap
          ( \(b0, c0) ->
              [ (b1, c0 * coeff)
              | (b1, coeff) <-
                  decompose @(FuseSpine U1 (FusedLeft U1 a ma b mb c mc))
                    ( flatF
                        ( basisValue
                            @(FuseSpine U1 (FusedRight U1 a ma b mb c mc))
                            b0
                        )
                    )
              ]
          )

instance
  ( KnownNat a
  , KnownNat b
  , KnownNat c
  , KnownNat ma
  , KnownNat mb
  , KnownNat mc
  , r ~ Flat SU2 (Leaf SU2 a ma)
  , q ~ Flat SU2 (Leaf SU2 b mb)
  , s ~ Flat SU2 (Leaf SU2 c mc)
  , left ~ Flat SU2 (FusedLeft SU2 a ma b mb c mc)
  , right ~ Flat SU2 (FusedRight SU2 a ma b mb c mc)
  , stLeft ~ STLeft SG.SU2 r q s
  , stRight ~ STRight SG.SU2 r q s
  , KnownRep SG.SU2 r
  , KnownRep SG.SU2 q
  , KnownRep SG.SU2 s
  , KnownRep SG.SU2 (ST.Tensor SG.SU2 r q)
  , KnownRep SG.SU2 (ST.Tensor SG.SU2 q s)
  , KnownRep SG.SU2 stLeft
  , KnownRep SG.SU2 stRight
  , UnpackFusedFlat SU2 (FusedLeft SU2 a ma b mb c mc)
  , UnpackFusedFlat SU2 (FusedRight SU2 a ma b mb c mc)
  , FusedToArray (FusedLeftSpine SU2 a ma b mb c mc)
  , FusedToArray (FusedRightSpine SU2 a ma b mb c mc)
  , PackSchur (IntertwinerHom SG.SU2 stLeft stRight)
  , PackSchur (IntertwinerHom SG.SU2 stRight stLeft)
  , RepListG SG.SU2 stLeft
  , RepListG SG.SU2 stRight
  , KnownNat (RepDimG SG.SU2 stLeft)
  , KnownNat (RepDimG SG.SU2 stRight)
  , RepDimG SG.SU2 left ~ RepDimG SG.SU2 stLeft
  , RepDimG SG.SU2 right ~ RepDimG SG.SU2 stRight
  , HasBasis (FuseSpine SU2 (FusedLeft SU2 a ma b mb c mc))
  , HasBasis (FuseSpine SU2 (FusedRight SU2 a ma b mb c mc))
  , Scalar (FuseSpine SU2 (FusedLeft SU2 a ma b mb c mc)) ~ Complex Double
  , Scalar (FuseSpine SU2 (FusedRight SU2 a ma b mb c mc)) ~ Complex Double
  ) =>
  CanFmove SU2 a ma b mb c mc
  where
  fmove =
    recompose @(FuseSpine SU2 (FusedRight SU2 a ma b mb c mc))
      . f
      . decompose @(FuseSpine SU2 (FusedLeft SU2 a ma b mb c mc))
    where
      mor = fSymbolHomSU2 (Proxy @r) (Proxy @q) (Proxy @s)
      flatF t =
        unpackFusedFlat @SU2 @(FusedRight SU2 a ma b mb c mc) $
          applyFlatInter @SG.SU2 @stLeft @stRight mor (fusedToArray t)
      f =
        concatMap
          ( \(b0, c0) ->
              [ (b1, c0 * coeff)
              | (b1, coeff) <-
                  decompose @(FuseSpine SU2 (FusedRight SU2 a ma b mb c mc))
                    ( flatF
                        ( basisValue
                            @(FuseSpine SU2 (FusedLeft SU2 a ma b mb c mc))
                            b0
                        )
                    )
              ]
          )

  fmoveInv =
    recompose @(FuseSpine SU2 (FusedLeft SU2 a ma b mb c mc))
      . f
      . decompose @(FuseSpine SU2 (FusedRight SU2 a ma b mb c mc))
    where
      mor = fSymbolHomSU2Inv (Proxy @r) (Proxy @q) (Proxy @s)
      flatF t =
        unpackFusedFlat @SU2 @(FusedLeft SU2 a ma b mb c mc) $
          applyFlatInter @SG.SU2 @stRight @stLeft mor (fusedToArray t)
      f =
        concatMap
          ( \(b0, c0) ->
              [ (b1, c0 * coeff)
              | (b1, coeff) <-
                  decompose @(FuseSpine SU2 (FusedLeft SU2 a ma b mb c mc))
                    ( flatF
                        ( basisValue
                            @(FuseSpine SU2 (FusedRight SU2 a ma b mb c mc))
                            b0
                        )
                    )
              ]
          )
