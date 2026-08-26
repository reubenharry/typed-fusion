{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Flat-buffer oracles for 'Experiments.Symbolic' (CG fuse, unpack).
--
-- Production 'Experiments.Symbolic' keeps merge categorical via
-- 'TensorNetwork.Categorical'; tensor CG fuse remains @undefined@ there until
-- a typed intertwiner exists.
module Experiments.Symbolic.Reference
  ( SectorFlatDim
  , sectorFlatDim
  , TensorFusedFlat
  , fuseOneSectorTensorReference
  , fuseTensorReference
  ) where

import Data.Complex (Complex)
import Data.Proxy (Proxy (..))
import Experiments.Symbolic
import GHC.TypeLits (KnownNat, Nat, natVal, type (*))
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import Symmetry.CG.SU2 (fuseSU2Flat)
import qualified Symmetry.Group as SG
import Symmetry.RepSingleton (KnownRep (..))
import qualified Data.Vector.Storable as VS

-- | Flat @toArray@ length of one sector (Reference / buffer boundary only).
type family SectorFlatDim (s :: Sector) :: Nat where
  SectorFlatDim '( 'Atom j, μ) = EvalMult μ * IrrepDim j
  SectorFlatDim '( 'Tensor j1 j2, 'AtomM m) =
    m * IrrepDim j1 * IrrepDim j2
  SectorFlatDim '( 'Tensor j1 j2, 'Prod m n) =
    m * IrrepDim j1 * n * IrrepDim j2

sectorFlatDim :: forall s. KnownNat (SectorFlatDim s) => Proxy s -> Int
sectorFlatDim _ =
  fromIntegral (natVal (Proxy @(SectorFlatDim s)))

-- | Post-'fuseSU2Flat' atom spine (@'AtomM'@ on each CG channel).
type TensorFusedFlat (j1 :: Nat) (j2 :: Nat) (m :: Nat) (n :: Nat) =
  TagMult ('AtomM (m * n)) (FuseIrrep ('Tensor j1 j2))

-- | Split a flat CG buffer into an atom 'RepV' spine (Reference boundary).
class UnpackFusedRep (rs :: Rep) where
  unpackFusedRep :: VS.Vector (Complex Double) -> RepV rs

instance UnpackFusedRep '[] where
  unpackFusedRep _ = RNil

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim j)
  , KnownNat (SectorFlatDim '( 'Atom j, 'AtomM m))
  , UnpackFusedRep rest
  ) =>
  UnpackFusedRep ('( 'Atom j, 'AtomM m) ': rest)
  where
  unpackFusedRep flat =
    let d = sectorFlatDim (Proxy @'( 'Atom j, 'AtomM m))
        (here, restFlat) = VS.splitAt d flat
    in RConsAtomAtomM (unsafeFromArray here) (unpackFusedRep @rest restFlat)

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim j)
  , KnownNat (SectorFlatDim '( 'Atom j, 'Prod m n))
  , UnpackFusedRep rest
  ) =>
  UnpackFusedRep ('( 'Atom j, 'Prod m n) ': rest)
  where
  unpackFusedRep flat =
    let d = sectorFlatDim (Proxy @'( 'Atom j, 'Prod m n))
        (here, restFlat) = VS.splitAt d flat
    in RConsAtomProd (unsafeFromArray here) (unpackFusedRep @rest restFlat)

-- | Flat @fuseSU2Flat@ oracle for one tensor sector.
fuseOneSectorTensorReference
  :: forall j1 j2 m n
   . ( KnownNat j1
     , KnownNat j2
     , KnownNat m
     , KnownNat n
     , KnownNat (IrrepDim j1)
     , KnownNat (IrrepDim j2)
     , KnownRep SG.SU2 '[ '(j1, m)]
     , KnownRep SG.SU2 '[ '(j2, n)]
     , KnownNat (m * n)
     , UnpackFusedRep (TensorFusedFlat j1 j2 m n)
     )
  => ToVSector ('Tensor j1 j2) ('Prod m n)
  -> RepV (TensorFusedFlat j1 j2 m n)
fuseOneSectorTensorReference sec =
  unpackFusedRep @(TensorFusedFlat j1 j2 m n) $
    fuseSU2Flat
      (repSing @SG.SU2 @'[ '(j1, m)])
      (repSing @SG.SU2 @'[ '(j2, n)])
      (toArray sec)

-- | CG fuse a single-sector @'Tensor'@ via the flat oracle.
fuseTensorReference
  :: forall j1 m1 j2 m2
   . ( KnownNat j1
     , KnownNat m1
     , KnownNat j2
     , KnownNat m2
     , KnownNat (IrrepDim j1)
     , KnownNat (IrrepDim j2)
     , KnownRep SG.SU2 '[ '(j1, m1)]
     , KnownRep SG.SU2 '[ '(j2, m2)]
     , KnownSymbolicRep
         ( Tensor
             '[ '( 'Atom j1, 'AtomM m1)]
             '[ '( 'Atom j2, 'AtomM m2)]
         )
     , KnownSymbolicRep (TensorFusedFlat j1 j2 m1 m2)
     , KnownSymbolicRep (Coalesce (TensorFusedFlat j1 j2 m1 m2))
     , KnownNat (m1 * m2)
     , UnpackFusedRep (TensorFusedFlat j1 j2 m1 m2)
     )
  => RepV
       ( Tensor
           '[ '( 'Atom j1, 'AtomM m1)]
           '[ '( 'Atom j2, 'AtomM m2)]
       )
  -> RepV (Coalesce (TensorFusedFlat j1 j2 m1 m2))
fuseTensorReference (RConsTensorProd sv RNil) =
  coalesce @(TensorFusedFlat j1 j2 m1 m2) $
    fuseOneSectorTensorReference @j1 @j2 @m1 @m2 sv
fuseTensorReference _ =
  error "fuseTensorReference: expected single-sector Tensor spine"
