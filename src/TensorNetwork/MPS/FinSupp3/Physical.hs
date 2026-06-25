{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

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
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import Data.VectorSpace (sumV, VectorSpace ((*^)))
import Math.LinearMap.Category (type (⊗), Tensor (..), LinearMap (..))
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import Numeric.LinearAlgebra.Static (C, Sized (create, unwrap))
import Numeric.LinearAlgebra.Static.COrphans ()
import GHC.TypeLits (KnownNat, natVal)
import qualified Data.Vector.Storable as VS
import qualified Data.Vector as V
import TensorNetwork.MPS.FinSupp3.Internal
  ( Field, Bond (..), LeftSite (..), BulkSite (..), RightSite (..)
  , MPS (..), Physical3, PhysicalDim3, vpDim, unitBond, basisCvp )
import TensorNetwork.MPS.FinSupp3.VectorSpace (zeroMPS)
import TensorNetwork.MPS.FinSupp3.Reference (amplitude, flatIndex3)
import TensorNetwork.MPS.FinSupp3.Bond (offsetBond)
import Data.VectorSpace.Free.FiniteSupportedSequence (FinSuppSeq (..))
import qualified Data.Vector.Unboxed as U

mpsToTensor
  :: forall p. KnownNat p => MPS p -> Physical3 p
mpsToTensor mps =
  sumV
    [ amplitude mps s1 s2 s3 *^ (basisCvp @p s1 ⊗ (basisCvp @p s2 ⊗ basisCvp @p s3))
    | s1 <- [0 .. vp - 1], s2 <- [0 .. vp - 1], s3 <- [0 .. vp - 1] ]
  where vp = vpDim @p

mpsToFlat
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => MPS p -> C (PhysicalDim3 p)
mpsToFlat =
  unsafeFromArray . (toArray :: Physical3 p -> VS.Vector Complex) . mpsToTensor

physicalToFlat
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => Physical3 p -> C (PhysicalDim3 p)
physicalToFlat =
  unsafeFromArray . (toArray :: Physical3 p -> VS.Vector Complex)

physicalFromFlat
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => C (PhysicalDim3 p) -> Physical3 p
physicalFromFlat v = unsafeFromArray (unwrap v)

basisFlatIndex
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => Basis (Physical3 p) -> Int
basisFlatIndex b =
  flatIndex3 (vpDim @p) s1 s2 s3
  where
    (s1, (s2, s3)) = basisToTriple b

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
       (LeftSite (LinearMap (V.toList leftRows)))
       (BulkSite (LinearMap [Tensor (V.generate vp (\j -> if j == s2 then unitBond else FinSuppSeq U.empty))]))
       (RightSite (LinearMap [basisCvp @p s3]))

productMPSFromBasis
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => Basis (Physical3 p) -> MPS p
productMPSFromBasis b =
  let (s1, s2, s3) = physicalIndicesFromBasis b
  in productMPSAtIndices s1 s2 s3

mpsFromPhysical
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => Physical3 p -> MPS p
mpsFromPhysical phys =
  let vp = vpDim @p
      terms =
        [ (physicalIndicesFromBasis b, c)
        | (b, c) <- decompose phys
        , c /= 0
        ]
  in case terms of
       [] -> zeroMPS
       _  ->
         MPS
           (LeftSite (LinearMap (V.toList (mpsLeftRows vp terms))))
           (BulkSite (LinearMap (mpsCenterImgs vp terms)))
           (RightSite (LinearMap (mpsRightImgs terms)))

mpsLeftRows :: Int -> [((Int, Int, Int), Field)] -> V.Vector Bond
mpsLeftRows vp terms =
  V.generate vp $ \s1 ->
    FinSuppSeq $
      U.fromList [ if s1 == s1' then c else 0 | ((s1', _, _), c) <- terms ]

mpsCenterImgs :: Int -> [((Int, Int, Int), Field)] -> [C vp ⊗ Bond]
mpsCenterImgs vp terms =
  [ Tensor (V.generate vp $ \p -> if p == s2 then offsetBond i unitBond else FinSuppSeq U.empty)
  | (i, ((_, s2, _), _)) <- zip [0 ..] terms
  ]

mpsRightImgs :: forall p. KnownNat p => [((Int, Int, Int), Field)] -> [C p]
mpsRightImgs terms = [ basisCvp @p s3 | ((_, _, s3), _) <- terms ]

mpsFromFlat
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => C (PhysicalDim3 p) -> MPS p
mpsFromFlat = mpsFromPhysical . physicalFromFlat

canonicalMPS :: (KnownNat p, KnownNat (PhysicalDim3 p)) => MPS p -> MPS p
canonicalMPS = mpsFromPhysical . mpsToTensor

instance
  ( KnownNat p, KnownNat (PhysicalDim3 p) ) =>
  HasBasis (MPS p)
  where
  type Basis (MPS p) = Basis (Physical3 p)
  basisValue b = mpsFromPhysical (basisValue b :: Physical3 p)
  decompose m = decompose (mpsToTensor m)
  decompose' m = decompose' (mpsToTensor m)
