{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module TensorNetwork.MPS.FinSupp3.Physical
  ( mpsToTensor
  , mpsToFlat
  , physicalToFlat
  , physicalFromFlat
  , mpsFromPhysical
  , mpsFromFlat
  , canonicalMPS
  , productMPSAtIndices
  , productMPSFromBasis
  , allPhysicalBasis
  , flatBasisToPhysicalBasis
  , physicalIndicesFromBasis
  ) where

import Data.Basis (HasBasis (..))
import Data.Complex (Complex)
import Data.Finite (Finite, finites, getFinite)
import Data.Proxy (Proxy (..))
import Data.VectorSpace (VectorSpace ((*^)), sumV)
import Math.LinearMap.Category (type (⊗), Tensor (..), LinearMap (..))
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import Numeric.LinearAlgebra.Static (C, Sized (unwrap))
import Numeric.LinearAlgebra.Static.COrphans ()
import GHC.TypeLits (KnownNat)
import qualified Data.Vector.Storable as VS
import qualified Data.Vector as V
import TensorNetwork.MPS.FinSupp3.Internal
  ( Field, Bond (..), LeftSite (..), BulkSite (..), RightSite (..)
  , MPS (..), Physical3, PhysicalDim3, vpDim, unitBond, basisCvp )
import TensorNetwork.MPS.FinSupp3.VectorSpace (zeroMPS)
import TensorNetwork.MPS.FinSupp3.Contraction (mpsChainClose, permuteFlatLegs13)
import TensorNetwork.MPS.FinSupp3.Reference (flatIndex3)
import TensorNetwork.MPS.FinSupp3.Bond (offsetBond)
import Data.VectorSpace.Free.FiniteSupportedSequence (FinSuppSeq (..))
import qualified Data.Vector.Unboxed as U


-- | Rebuild 'Physical3' from categorically closed coefficients with @s₁ ↔ s₃@
-- leg order corrected via the physical basis (linear isomorphism on @p³@).
physicalFromClosedLegs
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => Physical3 p -> Physical3 p
physicalFromClosedLegs closed =
  let perm = permuteFlatLegs13 @p (toArray closed)
  in sumV
       [ perm VS.! basisFlatIndex b *^ basisValue b
       | b <- allPhysicalBasis @p
       ]

mpsToTensor
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => MPS p -> Physical3 p
mpsToTensor = physicalFromClosedLegs . mpsChainClose

mpsToFlat
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => MPS p -> C (PhysicalDim3 p)
mpsToFlat m =
  unsafeFromArray (permuteFlatLegs13 @p (toArray (mpsChainClose m)))

physicalToFlat
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => Physical3 p -> C (PhysicalDim3 p)
physicalToFlat =
  unsafeFromArray . (toArray :: Physical3 p -> VS.Vector Field)

physicalFromFlat
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => C (PhysicalDim3 p) -> Physical3 p
physicalFromFlat v = unsafeFromArray (unwrap v)

basisFlatIndex
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => Basis (Physical3 p) -> Int
basisFlatIndex b =
  let (s1, s2, s3) = basisToTriple b
  in flatIndex3 (vpDim @p) s1 s2 s3

basisToTriple :: Basis (Physical3 p) -> (Int, Int, Int)
basisToTriple b =
  let (i, (j, k)) = b
  in (fromIntegral (getFinite i), fromIntegral (getFinite j), fromIntegral (getFinite k))

physicalIndicesFromBasis
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => Basis (Physical3 p) -> (Int, Int, Int)
physicalIndicesFromBasis = basisToTriple

flatBasisToPhysicalBasis
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => Finite (PhysicalDim3 p) -> Basis (Physical3 p)
flatBasisToPhysicalBasis i =
  head [ b | b <- allPhysicalBasis @p, basisFlatIndex b == fromIntegral (getFinite i) ]

allPhysicalBasis :: forall p. KnownNat p => [Basis (Physical3 p)]
allPhysicalBasis =
  [ (b1, (b2, b3))
  | b1 <- finites @p
  , b2 <- finites @p
  , b3 <- finites @p
  ]

productMPSAtIndices
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => Int -> Int -> Int -> MPS p
productMPSAtIndices s1 s2 s3 =
  let vp = vpDim @p
      leftRows = V.generate vp (\j -> if j == s1 then unitBond else FinSuppSeq U.empty)
  in MPS
       (LeftSite (LinearMap leftRows))
       (BulkSite (LinearMap [Tensor (V.generate vp (\j -> if j == s2 then unitBond else FinSuppSeq U.empty))]))
       (RightSite (LinearMap [basisCvp @p s3]))

productMPSFromBasis
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => Basis (Physical3 p) -> MPS p
productMPSFromBasis b =
  let (s1, s2, s3) = physicalIndicesFromBasis b
  in productMPSAtIndices s1 s2 s3

mpsFromPhysical
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => Physical3 p -> MPS p
mpsFromPhysical = mpsFromFlatArray . toArray

mpsFromFlat
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => C (PhysicalDim3 p) -> MPS p
mpsFromFlat = mpsFromFlatArray . unwrap

mpsFromFlatArray
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => VS.Vector Field -> MPS p
mpsFromFlatArray arr =
  let vp = vpDim @p
      coeffs = VS.toList arr
      terms =
        [ ( physicalIndicesFromBasis (flatBasisToPhysicalBasis @p fin)
          , coeffs !! fromIntegral (getFinite fin)
          )
        | fin <- finites @(PhysicalDim3 p)
        , coeffs !! fromIntegral (getFinite fin) /= 0
        ]
  in case terms of
       [] -> zeroMPS
       _  ->
         MPS
           (LeftSite (LinearMap (mpsLeftRows vp terms)))
           (BulkSite (LinearMap (mpsCenterImgs vp terms)))
           (RightSite (LinearMap (mpsRightImgs @p terms)))

mpsLeftRows :: Int -> [((Int, Int, Int), Field)] -> V.Vector Bond
mpsLeftRows vp terms =
  V.generate vp $ \s1 ->
    FinSuppSeq $
      U.fromList [ if s1 == s1' then c else 0 | ((s1', _, _), c) <- terms ]

mpsCenterImgs
  :: forall p. KnownNat p => Int -> [((Int, Int, Int), Field)] -> [C p ⊗ Bond]
mpsCenterImgs _ terms =
  [ Tensor
      ( V.generate (vpDim @p) $ \row ->
          if row == s2 then offsetBond i unitBond else FinSuppSeq U.empty
      )
  | (i, ((_, s2, _), _)) <- zip [0 ..] terms
  ]

mpsRightImgs :: forall p. KnownNat p => [((Int, Int, Int), Field)] -> [C p]
mpsRightImgs terms = [ basisCvp @p s3 | ((_, _, s3), _) <- terms ]

canonicalMPS :: (KnownNat p, KnownNat (PhysicalDim3 p)) => MPS p -> MPS p
canonicalMPS = mpsFromPhysical . mpsToTensor

instance
  ( KnownNat p, KnownNat (PhysicalDim3 p) ) =>
  HasBasis (MPS p)
  where
  type Basis (MPS p) = Basis (Physical3 p)
  basisValue b = productMPSFromBasis b
  decompose m = decompose (mpsToTensor m)
  decompose' m = decompose' (mpsToTensor m)
