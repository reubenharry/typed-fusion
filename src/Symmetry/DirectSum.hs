{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Direct sums of representation spaces, including growable @InfRep@ keyed
-- by irrep label.
module Symmetry.DirectSum
  ( Sector (..)
  , IrrepSlot (..)
  , InfRep (..)
  , unInfRep
  , emptyInfRep
  , insertSector
  , lookupSector
  , irrepSlot
  , projectSector
  , maybeProjectSector
  , restrictSubspace
  , embedSector
  , embedSectorInto
  , ActsOn (..)
  , SectorTensor (..)
  , InfRepTensor (..)
  , unInfRepTensor
  , emptyInfRepTensor
  ) where

import Data.Kind (Type)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Singletons (Sing, fromSing)
import Data.Singletons.Decide ((%~), SDecide (..), Decision (Proved, Disproved))
import Data.Type.Equality ((:~:) (Refl))
import Unsafe.Coerce (unsafeCoerce)
import GHC.TypeLits (KnownNat, Nat, type (+))
import Numeric.LinearAlgebra.Static (C, konst)
import Numeric.LinearAlgebra.Static.COrphans ()
import Data.VectorSpace.Free (AdditiveGroup (..), VectorSpace (..))
import Symmetry.ChargeEq (chargeInteger)
import Symmetry.Utils (Z)
import Symmetry.ChargeEq ()  -- SDecide Z
import Symmetry.Group (Group (..), GroupElement, Irreps, IrrepDim)
import Symmetry.SU2 (applyWigner)
import Symmetry.Utils ()
import Data.Complex (Complex ((:+)))
import Data.VectorSpace (InnerSpace ((<.>)))
import Math.LinearMap.Category
  ( DimensionAware (..), TensorSpace (..), type (⊗), Scalar )
import Math.Manifold.Core.PseudoAffine
import Math.LinearMap.Asserted
  ( getLinearFunction, bilinearFunction, linearFunction )

-- | One direct-summand: irrep @j@ with a vector in @C (IrrepDim g j)@.
data Sector (g :: Group) where
  Sector
    :: KnownNat (IrrepDim g j)
    => Sing (j :: Irreps g) -> C (IrrepDim g j) -> Sector g

-- | Map key: existentially-packaged irrep label.
data IrrepSlot (g :: Group) where
  IrrepSlot :: Sing (j :: Irreps g) -> IrrepSlot g

-- | Finitely-supported @⊕_j V_j@; active sectors stored in a 'Map'.
newtype InfRep (g :: Group) = InfRep {unInfRep :: Map (IrrepSlot g) (Sector g)}

-- | Block @V_j ⊗ w@; per-group instances avoid ambiguous @Irreps g@ dispatch.
data family Block (g :: Group) (j :: Irreps g) (w :: Type) :: Type

data instance Block U1 (z :: Z) w where
  BlockU1 :: TensorProduct (C 1) w -> Block U1 z w
  BlockU1InfRep :: InfRepTensor h (C 1) -> Block U1 z (InfRep h)
  BlockU1InfRepTensor
    :: InfRepTensor h (TensorProduct (C 1) x) -> Block U1 z (InfRepTensor h x)

data instance Block SU2 (spin :: Nat) w where
  BlockSU2 :: TensorProduct (C (spin + 1)) w -> Block SU2 spin w
  BlockSU2InfRep :: InfRepTensor h (C (spin + 1)) -> Block SU2 spin (InfRep h)
  BlockSU2InfRepTensor
    :: InfRepTensor h (TensorProduct (C (spin + 1)) x)
    -> Block SU2 spin (InfRepTensor h x)

-- | One tensor sector: @V_j ⊗ w@.
data SectorTensor g w where
  SectorTensor
    :: KnownNat (IrrepDim g j)
    => Sing (j :: Irreps g) -> Block g j w -> SectorTensor g w

-- | @⊕_j (V_j ⊗ w)@ with the same sector keys as 'InfRep'.
newtype InfRepTensor g w = InfRepTensor
  { unInfRepTensor :: Map (IrrepSlot g) (SectorTensor g w) }

emptyInfRep :: InfRep g
emptyInfRep = InfRep Map.empty

emptyInfRepTensor :: InfRepTensor g w
emptyInfRepTensor = InfRepTensor Map.empty

insertSector
  :: (Ord (IrrepSlot g), KnownNat (IrrepDim g j))
  => Sing (j :: Irreps g) -> C (IrrepDim g j) -> InfRep g -> InfRep g
insertSector sj v (InfRep m) =
  InfRep (Map.insert (IrrepSlot sj) (Sector sj v) m)

lookupSector :: Ord (IrrepSlot g) => IrrepSlot g -> InfRep g -> Maybe (Sector g)
lookupSector k (InfRep m) = Map.lookup k m

irrepSlot :: Sing (j :: Irreps g) -> IrrepSlot g
irrepSlot = IrrepSlot

-- | Project onto the @j@-isotypical subspace; absent sectors yield zero.
projectSector
  :: ( Ord (IrrepSlot g), SDecide (Irreps g), KnownNat (IrrepDim g j)
     )
  => Sing (j :: Irreps g) -> InfRep g -> C (IrrepDim g j)
projectSector sj (InfRep m) =
  case Map.lookup (IrrepSlot sj) m of
    Just (Sector sj' v) ->
      case sj %~ sj' of
        Proved Refl -> unsafeCoerce v
        Disproved _ ->
          error "DirectSum.projectSector: irrep label mismatch (malformed InfRep map)"
    Nothing -> konst 0

maybeProjectSector
  :: ( Ord (IrrepSlot g), SDecide (Irreps g), KnownNat (IrrepDim g j)
     )
  => Sing (j :: Irreps g) -> InfRep g -> Maybe (C (IrrepDim g j))
maybeProjectSector sj (InfRep m) =
  case Map.lookup (IrrepSlot sj) m of
    Just (Sector sj' v) ->
      case sj %~ sj' of
        Proved Refl -> Just (unsafeCoerce v)
        Disproved _ ->
          error "DirectSum.maybeProjectSector: irrep label mismatch (malformed InfRep map)"
    Nothing -> Nothing

-- | Keep only the listed irrep sectors (subspace projection as a filter).
restrictSubspace
  :: Ord (IrrepSlot g) => [IrrepSlot g] -> InfRep g -> InfRep g
restrictSubspace slots (InfRep m) =
  InfRep (Map.restrictKeys m (Set.fromList slots))

-- | Embed a single irrep vector into @InfRep g@ (all other sectors zero).
embedSector
  :: (Ord (IrrepSlot g), KnownNat (IrrepDim g j))
  => Sing (j :: Irreps g) -> C (IrrepDim g j) -> InfRep g
embedSector sj v = insertSector sj v emptyInfRep

embedSectorInto
  :: (Ord (IrrepSlot g), KnownNat (IrrepDim g j))
  => Sing (j :: Irreps g) -> C (IrrepDim g j) -> InfRep g -> InfRep g
embedSectorInto = insertSector

--------------------------------------------------------------------------------
-- Group action
--------------------------------------------------------------------------------

u1PhaseFactorSing :: Sing (z :: Z) -> Double -> Complex Double
u1PhaseFactorSing sz theta =
  exp ((0 :+ 1) * (fromIntegral (chargeInteger sz) * theta :+ 0))

-- | Group action on representation carriers. Instances exist for each
-- vector-space type that knows its representation (@Sector g@, @InfRep g@, …).
class ActsOn (g :: Group) v where
  action :: GroupElement g -> v -> v

instance ActsOn U1 (Sector U1) where
  action ge (Sector sj v) = Sector sj (u1PhaseFactorSing sj ge *^ v)

instance ActsOn SU2 (Sector SU2) where
  action ge (Sector sj v) =
    let tj = fromIntegral (fromSing sj)
    in  Sector sj (applyWigner tj ge v)

instance (Ord (IrrepSlot g), ActsOn g (Sector g)) => ActsOn g (InfRep g) where
  action ge (InfRep m) =
    InfRep (Map.map (action @g @(Sector g) ge) m)

instance (Ord (IrrepSlot g), SDecide (Irreps g)) => AdditiveGroup (InfRep g) where
  zeroV = emptyInfRep
  InfRep m1 ^+^ InfRep m2 = InfRep (Map.unionWith addSector m1 m2)
  negateV (InfRep m) = InfRep (Map.map negateSector m)

addSector :: SDecide (Irreps g) => Sector g -> Sector g -> Sector g
addSector (Sector sa va) (Sector sb vb) =
  case sa %~ sb of
    Proved Refl -> Sector sa (va ^+^ vb)
    Disproved _ ->
      error "DirectSum.addSector: irrep labels differ (malformed InfRep map)"

negateSector :: Sector g -> Sector g
negateSector (Sector sj v) = Sector sj (negateV v)

scaleSector :: Complex Double -> Sector g -> Sector g
scaleSector μ (Sector sj v) = Sector sj (μ *^ v)

instance (Ord (IrrepSlot g), SDecide (Irreps g)) => VectorSpace (InfRep g) where
  type Scalar (InfRep g) = Complex Double
  μ *^ InfRep m = InfRep (Map.map (scaleSector μ) m)

instance (Ord (IrrepSlot g), SDecide (Irreps g)) => InnerSpace (InfRep g) where
  InfRep m1 <.> InfRep m2 =
    Map.foldl' (+) 0 (Map.intersectionWith innerSector m1 m2)

innerSector :: SDecide (Irreps g) => Sector g -> Sector g -> Complex Double
innerSector (Sector sa va) (Sector sb vb) =
  case sa %~ sb of
    Proved Refl -> va <.> vb
    Disproved _ -> 0

instance (Ord (IrrepSlot g), SDecide (Irreps g)) => DimensionAware (InfRep g) where
  type StaticDimension (InfRep g) = 'Nothing
  dimensionalityWitness = undefined

instance (Ord (IrrepSlot g), SDecide (Irreps g)) => Semimanifold (InfRep g) where
  type Needle (InfRep g) = InfRep g
  v .+~^ δ = v ^+^ δ

instance (Ord (IrrepSlot g), SDecide (Irreps g)) => PseudoAffine (InfRep g) where
  InfRep v .-~! InfRep w = InfRep v ^+^ negateV (InfRep w)
  InfRep v .-~. InfRep w = Just (InfRep v ^+^ negateV (InfRep w))

--------------------------------------------------------------------------------
-- Tensor sectors
--------------------------------------------------------------------------------

class AdditiveBlock g j w where
  addBlock :: Block g j w -> Block g j w -> Block g j w
  negateBlock :: Block g j w -> Block g j w
  scaleBlock :: Complex Double -> Block g j w -> Block g j w

instance
  {-# OVERLAPPABLE #-}
  ( TensorSpace w, Scalar w ~ Complex Double
  ) =>
  AdditiveBlock U1 z w
  where
  addBlock = error "DirectSum.addBlock: generic U1 block addition not yet wired"
  negateBlock = error "DirectSum.negateBlock: generic U1 block negation not yet wired"
  scaleBlock = error "DirectSum.scaleBlock: generic U1 block scaling not yet wired"

instance
  {-# OVERLAPPING #-}
  ( Ord (IrrepSlot h), SDecide (Irreps h)
  ) =>
  AdditiveBlock U1 z (InfRep h)
  where
  addBlock = error "DirectSum.addBlock: InfRep block addition not yet wired"
  negateBlock = error "DirectSum.negateBlock: InfRep block negation not yet wired"
  scaleBlock _ = error "DirectSum.scaleBlock: InfRep block scaling not yet wired"

instance
  {-# OVERLAPPING #-}
  ( TensorSpace x, Scalar x ~ Complex Double
  , Ord (IrrepSlot h), SDecide (Irreps h)
  ) =>
  AdditiveBlock U1 z (InfRepTensor h x)
  where
  addBlock = error "DirectSum.addBlock: InfRepTensor block addition not yet wired"
  negateBlock = error "DirectSum.negateBlock: InfRepTensor block negation not yet wired"
  scaleBlock _ = error "DirectSum.scaleBlock: InfRepTensor block scaling not yet wired"

instance
  {-# OVERLAPPABLE #-}
  ( KnownNat (spin + 1), TensorSpace w, Scalar w ~ Complex Double
  ) =>
  AdditiveBlock SU2 spin w
  where
  addBlock = error "DirectSum.addBlock: generic SU2 block addition not yet wired"
  negateBlock = error "DirectSum.negateBlock: generic SU2 block negation not yet wired"
  scaleBlock = error "DirectSum.scaleBlock: generic SU2 block scaling not yet wired"

instance
  {-# OVERLAPPING #-}
  ( KnownNat (spin + 1), Ord (IrrepSlot h), SDecide (Irreps h)
  ) =>
  AdditiveBlock SU2 spin (InfRep h)
  where
  addBlock = error "DirectSum.addBlock: InfRep block addition not yet wired"
  negateBlock = error "DirectSum.negateBlock: InfRep block negation not yet wired"
  scaleBlock _ = error "DirectSum.scaleBlock: InfRep block scaling not yet wired"

instance
  {-# OVERLAPPING #-}
  ( KnownNat (spin + 1), TensorSpace x, Scalar x ~ Complex Double
  , Ord (IrrepSlot h), SDecide (Irreps h)
  ) =>
  AdditiveBlock SU2 spin (InfRepTensor h x)
  where
  -- Inner sectors live in @InfRepTensor h (TensorProduct (C (spin + 1)) x)@.
  addBlock = error "DirectSum.addBlock: InfRepTensor block addition not yet wired"
  negateBlock = error "DirectSum.negateBlock: InfRepTensor block negation not yet wired"
  scaleBlock _ = error "DirectSum.scaleBlock: InfRepTensor block scaling not yet wired"

class AddSectorTensorOps g w where
  addSectorTensor
    :: SDecide (Irreps g) => SectorTensor g w -> SectorTensor g w -> SectorTensor g w
  negateSectorTensor :: SectorTensor g w -> SectorTensor g w
  scaleSectorTensor :: Complex Double -> SectorTensor g w -> SectorTensor g w

instance
  ( TensorSpace w, Scalar w ~ Complex Double
  ) =>
  AddSectorTensorOps U1 w
  where
  addSectorTensor (SectorTensor (sa :: Sing z) ta) (SectorTensor sb tb) =
    case sa %~ sb of
      Proved Refl -> SectorTensor sa (addBlock @U1 @z ta tb)
      Disproved _ ->
        error "DirectSum.addSectorTensor: irrep labels differ (malformed InfRepTensor map)"
  negateSectorTensor (SectorTensor (sj :: Sing z) t) =
    SectorTensor sj (negateBlock @U1 @z t)
  scaleSectorTensor μ (SectorTensor (sj :: Sing z) t) =
    SectorTensor sj (scaleBlock @U1 @z μ t)

instance
  ( KnownNat (spin + 1), TensorSpace w, Scalar w ~ Complex Double
  ) =>
  AddSectorTensorOps SU2 w
  where
  addSectorTensor (SectorTensor (sa :: Sing j) ta) (SectorTensor sb tb) =
    case sa %~ sb of
      Proved Refl -> SectorTensor sa (addBlock @SU2 @j ta tb)
      Disproved _ ->
        error "DirectSum.addSectorTensor: irrep labels differ (malformed InfRepTensor map)"
  negateSectorTensor (SectorTensor (sj :: Sing j) t) =
    SectorTensor sj (negateBlock @SU2 @j t)
  scaleSectorTensor μ (SectorTensor (sj :: Sing j) t) =
    SectorTensor sj (scaleBlock @SU2 @j μ t)

instance
  ( Ord (IrrepSlot U1), SDecide (Irreps U1)
  , TensorSpace w, Scalar w ~ Complex Double
  , AddSectorTensorOps U1 w
  ) =>
  AdditiveGroup (InfRepTensor U1 w)
  where
  zeroV = emptyInfRepTensor
  InfRepTensor m1 ^+^ InfRepTensor m2 =
    InfRepTensor (Map.unionWith addSectorTensor m1 m2)
  negateV (InfRepTensor m) = InfRepTensor (Map.map negateSectorTensor m)

instance
  ( Ord (IrrepSlot SU2), SDecide (Irreps SU2)
  , TensorSpace w, Scalar w ~ Complex Double
  , AddSectorTensorOps SU2 w
  ) =>
  AdditiveGroup (InfRepTensor SU2 w)
  where
  zeroV = emptyInfRepTensor
  InfRepTensor m1 ^+^ InfRepTensor m2 =
    InfRepTensor (Map.unionWith addSectorTensor m1 m2)
  negateV (InfRepTensor m) = InfRepTensor (Map.map negateSectorTensor m)

instance
  ( Ord (IrrepSlot U1), SDecide (Irreps U1)
  , TensorSpace w, Scalar w ~ Complex Double
  , AddSectorTensorOps U1 w
  ) =>
  VectorSpace (InfRepTensor U1 w)
  where
  type Scalar (InfRepTensor U1 w) = Complex Double
  μ *^ InfRepTensor m = InfRepTensor (Map.map (scaleSectorTensor μ) m)

instance
  ( Ord (IrrepSlot SU2), SDecide (Irreps SU2)
  , TensorSpace w, Scalar w ~ Complex Double
  , AddSectorTensorOps SU2 w
  ) =>
  VectorSpace (InfRepTensor SU2 w)
  where
  type Scalar (InfRepTensor SU2 w) = Complex Double
  μ *^ InfRepTensor m = InfRepTensor (Map.map (scaleSectorTensor μ) m)

applyBlockTensor
  :: forall g j w.
     ( KnownNat (IrrepDim g j), MakeBlockTensor g j w
     )
  => C (IrrepDim g j) -> w -> Block g j w
applyBlockTensor v w = makeBlockTensor @g @j v w

class MakeBlockTensor g j w where
  makeBlockTensor :: C (IrrepDim g j) -> w -> Block g j w

instance {-# OVERLAPPABLE #-} (TensorSpace w, Scalar w ~ Complex Double) => MakeBlockTensor U1 z w where
  makeBlockTensor = undefined

instance
  {-# OVERLAPPING #-}
  ( Ord (IrrepSlot h), SDecide (Irreps h)
  ) =>
  MakeBlockTensor U1 z (InfRep h)
  where
  makeBlockTensor v (InfRep m) =
    BlockU1InfRep (tensorCWithInfRep @U1 @h v (InfRep m))

instance
  {-# OVERLAPPABLE #-}
  ( KnownNat (spin + 1), TensorSpace w, Scalar w ~ Complex Double
  ) =>
  MakeBlockTensor SU2 spin w
  where
  makeBlockTensor = undefined

instance
  {-# OVERLAPPING #-}
  ( KnownNat (spin + 1), Ord (IrrepSlot h), SDecide (Irreps h)
  ) =>
  MakeBlockTensor SU2 spin (InfRep h)
  where
  makeBlockTensor v (InfRep m) =
    BlockSU2InfRep (tensorCWithInfRep @SU2 @h v (InfRep m))

class TensorWithInfRep g h where
  tensorCWithInfRep
    :: forall j.
       KnownNat (IrrepDim g j) =>
       C (IrrepDim g j) -> InfRep h -> InfRepTensor h (C (IrrepDim g j))

instance TensorWithInfRep U1 h where
  tensorCWithInfRep = undefined

instance TensorWithInfRep SU2 h where
  tensorCWithInfRep = undefined

class TensorSectorWith g w where
  tensorSectorWith :: w -> Sector g -> SectorTensor g w

instance (TensorSpace w, Scalar w ~ Complex Double) => TensorSectorWith U1 w where
  tensorSectorWith w (Sector (sj :: Sing z) v) =
    SectorTensor sj (makeBlockTensor @U1 @z v w)

instance
  ( KnownNat (spin + 1), TensorSpace w, Scalar w ~ Complex Double
  ) =>
  TensorSectorWith SU2 w
  where
  tensorSectorWith w (Sector (sj :: Sing j) v) =
    SectorTensor sj (makeBlockTensor @SU2 @j v w)

class TensorBlockWith g j w x where
  tensorBlockWith :: Block g j w -> x -> Block g j (TensorProduct w x)

instance TensorBlockWith U1 z w x where
  tensorBlockWith = error "DirectSum.tensorBlockWith: not yet wired"

instance TensorBlockWith U1 z (InfRep h) x where
  tensorBlockWith = error "DirectSum.tensorBlockWith: InfRep RHS tensor not yet wired"

instance TensorBlockWith U1 z (InfRepTensor h x) y where
  tensorBlockWith = error "DirectSum.tensorBlockWith: InfRepTensor nesting not yet wired"

instance TensorBlockWith SU2 spin w x where
  tensorBlockWith = error "DirectSum.tensorBlockWith: not yet wired"

instance TensorBlockWith SU2 spin (InfRep h) x where
  tensorBlockWith = error "DirectSum.tensorBlockWith: InfRep RHS tensor not yet wired"

instance TensorBlockWith SU2 spin (InfRepTensor h x) y where
  tensorBlockWith = error "DirectSum.tensorBlockWith: InfRepTensor nesting not yet wired"

tensorInfRepTensorWith
  :: forall h n x.
     ( KnownNat n, Ord (IrrepSlot h), SDecide (Irreps h)
     , TensorSpace x, Scalar x ~ Complex Double
     )
  => InfRepTensor h (C n) -> x -> InfRepTensor h (TensorProduct (C n) x)
tensorInfRepTensorWith = undefined

wellDefinedSectorTensor
  :: (TensorSpace w, Scalar w ~ Complex Double) => SectorTensor g w -> Maybe (SectorTensor g w)
wellDefinedSectorTensor (SectorTensor sj t) = Just (SectorTensor sj t)

instance (Ord (IrrepSlot g), SDecide (Irreps g)) => TensorSpace (InfRep g) where
  type TensorProduct (InfRep g) w = InfRepTensor g w
  scalarSpaceWitness = undefined
  linearManifoldWitness = undefined
  zeroTensor = undefined
  toFlatTensor = undefined
  fromFlatTensor = undefined
  addTensors = undefined
  subtractTensors = undefined
  negateTensor = undefined
  scaleTensor = undefined
  tensorProduct = undefined
  transposeTensor = undefined
  fmapTensor = undefined
  fzipTensorWith = undefined
  tensorUnsafeFromArrayWithOffset = undefined
  tensorUnsafeWriteArrayWithOffset = undefined
  coerceFmapTensorProduct = undefined
  wellDefinedVector (InfRep m) =
    InfRep <$> traverse wellDefinedSector m
  wellDefinedTensor = undefined
  vectorConjugate = undefined

wellDefinedSector :: Sector g -> Maybe (Sector g)
wellDefinedSector (Sector sj v) = Sector sj <$> wellDefinedVector v

-- | @InfRep g ⊗ w@ as a sector-keyed tensor; use until linearmap @⊗@ coercions
-- are wired like 'Symmetry.Orphans'.
tensorProductInfRep
  :: forall g w.
     ( Ord (IrrepSlot g), SDecide (Irreps g)
     , TensorSpace w, Scalar w ~ Complex Double
     ) =>
     InfRep g -> w -> InfRepTensor g w
tensorProductInfRep = undefined

--------------------------------------------------------------------------------
-- Map keys: total order on irrep labels
--------------------------------------------------------------------------------

instance Ord (IrrepSlot SU2) where
  compare (IrrepSlot a) (IrrepSlot b) =
    compare (fromSing a) (fromSing b)

instance Ord (IrrepSlot U1) where
  compare (IrrepSlot a) (IrrepSlot b) =
    compare (chargeInteger a) (chargeInteger b)

instance Eq (IrrepSlot SU2) where
  IrrepSlot a == IrrepSlot b =
    case a %~ b of
      Proved _ -> True
      Disproved _ -> False

instance Eq (IrrepSlot U1) where
  IrrepSlot a == IrrepSlot b =
    case a %~ b of
      Proved _ -> True
      Disproved _ -> False

instance Eq (Sector SU2) where
  Sector sa va == Sector sb vb =
    case sa %~ sb of
      Proved Refl -> va == vb
      Disproved _ -> False

instance Eq (Sector U1) where
  Sector sa va == Sector sb vb =
    case sa %~ sb of
      Proved Refl -> va == vb
      Disproved _ -> False

instance Eq (InfRep SU2) where
  InfRep m1 == InfRep m2 = m1 == m2

instance Eq (InfRep U1) where
  InfRep m1 == InfRep m2 = m1 == m2
