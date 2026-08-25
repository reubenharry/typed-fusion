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
{-# OPTIONS_GHC -Wno-orphans #-}
{- HLINT ignore "Eta reduce" -}

-- | Leaf / multiplicity-block fusion experiments.
--
-- Type-level fusion spines are 'Tensor' (@Coalesce ∘ TensorRaw@). Unfused @r ⊗ q@
-- is 'Unfuse' (= 'HList' of 'UnfuseRaw' pair tensors, same order as 'TensorRaw').
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
-- Call sites use group-indexed 'Coalesce' / 'Tensor' / …. Workers stay
-- U1-/SU2-specialized: GHC rejects closed-TF equations with polymorphic @g@
-- when an argument kind mentions @Irreps g@ (@Irreps@ is a type family).
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

-- | Fused @r ⊗ q@.
type Fuse g r q = HList (RepToVectors g (Tensor g r q))

type UnfusePair g x y =
  Sector g (Fst x) (Snd x) ⊗ Sector g (Fst y) (Snd y)

-- | All pair tensors for one left sector against every right sector.
type UnfuseOne
  :: forall (g :: Group)
  -> (Irreps g, Multiplicity)
  -> [(Irreps g, Multiplicity)]
  -> [Type]
type family UnfuseOne g x q where
  UnfuseOne U1 x '[] = '[]
  UnfuseOne SU2 x '[] = '[]
  UnfuseOne U1 x ('(j, n) ': qs) =
    UnfusePair U1 x '(j, n) ': UnfuseOne U1 x qs
  UnfuseOne SU2 x ('(j, n) ': qs) =
    UnfusePair SU2 x '(j, n) ': UnfuseOne SU2 x qs

-- | Unfused @r ⊗ q@ as direct sum of pair tensors ('TensorRaw' order).
type UnfuseRaw
  :: forall (g :: Group)
  -> [(Irreps g, Multiplicity)]
  -> [(Irreps g, Multiplicity)]
  -> [Type]
type family UnfuseRaw g r q where
  UnfuseRaw U1 '[] _ = '[]
  UnfuseRaw SU2 '[] _ = '[]
  UnfuseRaw U1 ('(i, m) ': rs) q =
    Append (UnfuseOne U1 '(i, m) q) (UnfuseRaw U1 rs q)
  UnfuseRaw SU2 ('(i, m) ': rs) q =
    Append (UnfuseOne SU2 '(i, m) q) (UnfuseRaw SU2 rs q)

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
     , UnfuseRaw g '[ '(a, m)] '[ '(b, n)]
         ~ '[UnfusePair g '(a, m) '(b, n)]
     )
  => Sector g a m
  -> Sector g b n
  -> Unfuse g '[ '(a, m)] '[ '(b, n)]
tensorSectors ua vb = (ua ⊗ vb) :& HNil

swapUnfuse
  :: forall g a m b n.
     ( KnownNat m
     , KnownNat n
     , KnownNat (IrrepDim g a)
     , KnownNat (IrrepDim g b)
     , Sector g a m ~ (C m ⊗ C (IrrepDim g a))
     , Sector g b n ~ (C n ⊗ C (IrrepDim g b))
     , UnfuseRaw g '[ '(a, m)] '[ '(b, n)]
         ~ '[UnfusePair g '(a, m) '(b, n)]
     , UnfuseRaw g '[ '(b, n)] '[ '(a, m)]
         ~ '[UnfusePair g '(b, n) '(a, m)]
     )
  => Unfuse g '[ '(a, m)] '[ '(b, n)]
  -> Unfuse g '[ '(b, n)] '[ '(a, m)]
swapUnfuse (t :& HNil) = (swapMap $ t) :& HNil

-- | Flatten unfused pair-tensor 'HList' in 'UnfuseRaw' order.
class UnfuseOneToArray g x q where
  unfuseOneToArray :: HList (UnfuseOne g x q) -> VS.Vector (Complex Double)

instance UnfuseOneToArray U1 x '[] where
  unfuseOneToArray HNil = VS.empty

instance UnfuseOneToArray SU2 x '[] where
  unfuseOneToArray HNil = VS.empty

instance
  ( x ~ '(i, m)
  , KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim U1 i)
  , KnownNat (IrrepDim U1 j)
  , UnfuseOneToArray U1 x qs
  , UnfuseOne U1 x ('(j, n) ': qs)
      ~ (UnfusePair U1 x '(j, n) ': UnfuseOne U1 x qs)
  ) =>
  UnfuseOneToArray U1 x ('(j, n) ': qs)
  where
  unfuseOneToArray (t :& rest) =
    VS.concat [toArray t, unfuseOneToArray @U1 @x @qs rest]

instance
  ( x ~ '(i, m)
  , KnownNat i
  , KnownNat j
  , KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim SU2 i)
  , KnownNat (IrrepDim SU2 j)
  , UnfuseOneToArray SU2 x qs
  , UnfuseOne SU2 x ('(j, n) ': qs)
      ~ (UnfusePair SU2 x '(j, n) ': UnfuseOne SU2 x qs)
  ) =>
  UnfuseOneToArray SU2 x ('(j, n) ': qs)
  where
  unfuseOneToArray (t :& rest) =
    VS.concat [toArray t, unfuseOneToArray @SU2 @x @qs rest]

class SplitUnfuseOne g x q rest where
  splitUnfuseOne
    :: HList (Append (UnfuseOne g x q) rest)
    -> (HList (UnfuseOne g x q), HList rest)

instance SplitUnfuseOne U1 x '[] rest where
  splitUnfuseOne xs = (HNil, xs)

instance SplitUnfuseOne SU2 x '[] rest where
  splitUnfuseOne xs = (HNil, xs)

instance
  ( SplitUnfuseOne U1 x qs rest
  , UnfuseOne U1 x ('(j, n) ': qs)
      ~ (UnfusePair U1 x '(j, n) ': UnfuseOne U1 x qs)
  ) =>
  SplitUnfuseOne U1 x ('(j, n) ': qs) rest
  where
  splitUnfuseOne (t :& xs) =
    let (here, rest') = splitUnfuseOne @U1 @x @qs @rest xs
    in (t :& here, rest')

instance
  ( SplitUnfuseOne SU2 x qs rest
  , UnfuseOne SU2 x ('(j, n) ': qs)
      ~ (UnfusePair SU2 x '(j, n) ': UnfuseOne SU2 x qs)
  ) =>
  SplitUnfuseOne SU2 x ('(j, n) ': qs) rest
  where
  splitUnfuseOne (t :& xs) =
    let (here, rest') = splitUnfuseOne @SU2 @x @qs @rest xs
    in (t :& here, rest')

class UnfuseToArray g r q where
  unfuseToArray :: Unfuse g r q -> VS.Vector (Complex Double)

instance UnfuseToArray U1 '[] q where
  unfuseToArray HNil = VS.empty

instance UnfuseToArray SU2 '[] q where
  unfuseToArray HNil = VS.empty

instance
  ( UnfuseOneToArray U1 '(i, m) q
  , UnfuseToArray U1 rs q
  , UnfuseRaw U1 ('(i, m) ': rs) q
      ~ Append (UnfuseOne U1 '(i, m) q) (UnfuseRaw U1 rs q)
  , SplitUnfuseOne U1 '(i, m) q (UnfuseRaw U1 rs q)
  ) =>
  UnfuseToArray U1 ('(i, m) ': rs) q
  where
  unfuseToArray hs =
    let (here, rest) = splitUnfuseOne @U1 @'(i, m) @q @(UnfuseRaw U1 rs q) hs
    in VS.concat
         [ unfuseOneToArray @U1 @'(i, m) @q here
         , unfuseToArray @U1 @rs @q rest
         ]

instance
  ( UnfuseOneToArray SU2 '(i, m) q
  , UnfuseToArray SU2 rs q
  , UnfuseRaw SU2 ('(i, m) ': rs) q
      ~ Append (UnfuseOne SU2 '(i, m) q) (UnfuseRaw SU2 rs q)
  , SplitUnfuseOne SU2 '(i, m) q (UnfuseRaw SU2 rs q)
  ) =>
  UnfuseToArray SU2 ('(i, m) ': rs) q
  where
  unfuseToArray hs =
    let (here, rest) = splitUnfuseOne @SU2 @'(i, m) @q @(UnfuseRaw SU2 rs q) hs
    in VS.concat
         [ unfuseOneToArray @SU2 @'(i, m) @q here
         , unfuseToArray @SU2 @rs @q rest
         ]

--------------------------------------------------------------------------------
-- fuse = recompose . f . decompose
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

-- | Fusion intertwiner @Φ : unfused → fused@ via @recompose . f . decompose@.
class CanFuse g r q where
  fuse :: Unfuse g r q -> Fuse g r q

instance
  ( KnownNat a
  , KnownNat b
  , KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim SU2 a)
  , KnownNat (IrrepDim SU2 b)
  , KnownRep SG.SU2 '[ '(a, m) ]
  , KnownRep SG.SU2 '[ '(b, n) ]
  , UnpackFusedFlat SU2 (Tensor SU2 '[ '(a, m)] '[ '(b, n)])
  , UnfuseToArray SU2 '[ '(a, m)] '[ '(b, n)]
  , HasBasis (Unfuse SU2 '[ '(a, m)] '[ '(b, n)])
  , HasBasis (Fuse SU2 '[ '(a, m)] '[ '(b, n)])
  , Scalar (Unfuse SU2 '[ '(a, m)] '[ '(b, n)]) ~ Complex Double
  , Scalar (Fuse SU2 '[ '(a, m)] '[ '(b, n)]) ~ Complex Double
  ) =>
  CanFuse SU2 '[ '(a, m)] '[ '(b, n)]
  where
  fuse =
    recompose @(Fuse SU2 '[ '(a, m)] '[ '(b, n)])
      . f
      . decompose @(Unfuse SU2 '[ '(a, m)] '[ '(b, n)])
    where
      flatFuse t =
        unpackFusedFlat @SU2 @(Tensor SU2 '[ '(a, m)] '[ '(b, n)]) $
          fuseSU2Flat
            (repSing @SG.SU2 @'[ '(a, m) ])
            (repSing @SG.SU2 @'[ '(b, n) ])
            (unfuseToArray @SU2 @'[ '(a, m)] @'[ '(b, n)] t)
      f =
        concatMap
          ( \(b, c) ->
              [ (b', c * coeff)
              | (b', coeff) <-
                  decompose @(Fuse SU2 '[ '(a, m)] '[ '(b, n)])
                    (flatFuse (basisValue @(Unfuse SU2 '[ '(a, m)] '[ '(b, n)]) b))
              ]
          )

instance
  ( KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim U1 a)
  , KnownNat (IrrepDim U1 b)
  , SingI a
  , SingI b
  , KnownRep SG.U1 '[ '(a, m) ]
  , KnownRep SG.U1 '[ '(b, n) ]
  , UnpackFusedFlat U1 (Tensor U1 '[ '(a, m)] '[ '(b, n)])
  , UnfuseToArray U1 '[ '(a, m)] '[ '(b, n)]
  , HasBasis (Unfuse U1 '[ '(a, m)] '[ '(b, n)])
  , HasBasis (Fuse U1 '[ '(a, m)] '[ '(b, n)])
  , Scalar (Unfuse U1 '[ '(a, m)] '[ '(b, n)]) ~ Complex Double
  , Scalar (Fuse U1 '[ '(a, m)] '[ '(b, n)]) ~ Complex Double
  ) =>
  CanFuse U1 '[ '(a, m)] '[ '(b, n)]
  where
  fuse =
    recompose @(Fuse U1 '[ '(a, m)] '[ '(b, n)])
      . f
      . decompose @(Unfuse U1 '[ '(a, m)] '[ '(b, n)])
    where
      flatFuse t =
        unpackFusedFlat @U1 @(Tensor U1 '[ '(a, m)] '[ '(b, n)]) $
          fuseU1Flat
            (repSing @SG.U1 @'[ '(a, m) ])
            (repSing @SG.U1 @'[ '(b, n) ])
            (unfuseToArray @U1 @'[ '(a, m)] @'[ '(b, n)] t)
      f =
        concatMap
          ( \(b, c) ->
              [ (b', c * coeff)
              | (b', coeff) <-
                  decompose @(Fuse U1 '[ '(a, m)] '[ '(b, n)])
                    (flatFuse (basisValue @(Unfuse U1 '[ '(a, m)] '[ '(b, n)]) b))
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
swapCopyGrid
  :: forall m n. (KnownNat m, KnownNat n, KnownNat (Scale m n))
  => C (Scale m n)
  -> C (Scale m n)
swapCopyGrid c =
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
  (arr (linearFunction (swapCopyGrid @m @n)) ⊗^ (id :: C d +> C d)) $ sec

-- | Braiding on fused @r ⊗ q@ (spine walk; U(1) identity, SU(2) R-phase + copy swap).
class CanRmove g r q rs where
  rmove :: HList (RepToVectors g rs) -> HList (RepToVectors g rs)

instance CanRmove U1 r q '[] where
  rmove HNil = HNil

instance CanRmove SU2 r q '[] where
  rmove HNil = HNil

instance
  ( RepToVectors U1 ('(j, m) ': rs)
      ~ (Sector U1 j m ': RepToVectors U1 rs)
  , CanRmove U1 r q rs
  ) =>
  CanRmove U1 r q ('(j, m) ': rs)
  where
  rmove = id

instance
  ( r ~ '[ '(a, m)]
  , q ~ '[ '(b, n)]
  , KnownNat a
  , KnownNat b
  , KnownNat m
  , KnownNat n
  , KnownNat j
  , KnownNat k
  , k ~ Scale m n
  , KnownNat (IrrepDim SU2 j)
  , RepToVectors SU2 ('(j, k) ': rs)
      ~ (Sector SU2 j k ': RepToVectors SU2 rs)
  , CanRmove SU2 r q rs
  ) =>
  CanRmove SU2 r q ('(j, k) ': rs)
  where
  rmove (sec :& rest) =
    swapCopyGridSector @m @n @(IrrepDim SU2 j)
      (rPhaseSector @a @b @j @k sec)
      :& rmove @SU2 @r @q @rs rest
