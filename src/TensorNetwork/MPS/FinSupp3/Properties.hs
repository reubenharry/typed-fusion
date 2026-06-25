{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

module TensorNetwork.MPS.FinSupp3.Properties
  ( smallComplex
  , genCvp
  , genBond
  , genMPS
  , genMPO
  , prop_addThenFlatten
  , prop_addThenFlattenVP2
  , prop_addThenFlattenVP3
  , prop_basisMPSMatchesPhysicalVP2
  , prop_basisMPSMatchesPhysicalVP3
  , prop_decomposePrimeMatchesPhysicalVP2
  , prop_decomposePrimeMatchesPhysicalVP3
  , prop_physicalRecomposeVP2
  , prop_physicalRecomposeVP3
  , prop_mpsFromFlatRoundTripVP2
  , prop_mpsFromFlatRoundTripVP3
  , prop_mpsToFlatMatchesReferenceVP2
  , prop_mpsToFlatMatchesReferenceVP3
  , prop_mpoApplyFlatMatchesReferenceVP2
  , prop_composeMPOMatchesFlatVP2
  , prop_identityMPOVP2
  ) where

import Data.Complex (Complex ((:+)))
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import GHC.TypeLits (KnownNat, natVal)
import Math.LinearMap.Category (LinearMap (..), Tensor (..), getLinearMap)
import Math.LinearMap.Category.Instances ()
import Numeric.LinearAlgebra.Static (C, Sized (create))
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import qualified Numeric.LinearAlgebra as LA
import qualified Test.QuickCheck as QC
import qualified Control.Applicative as App
import Control.Monad (replicateM)
import Data.Basis (HasBasis (basisValue), decompose')
import Data.VectorSpace (AdditiveGroup ((^+^)))
import TensorNetwork.MPS.FinSupp3.Internal
  ( Field, Bond (..), LeftSite (..), BulkSite (..), RightSite (..)
  , OpLeft (..), OpBulk (..), OpRight (..), MPS (..), MPO (..), Physical3
  , PhysicalDim3 )
import TensorNetwork.MPS.FinSupp3.Physical
  ( mpsToFlat, mpsToTensor, mpsFromFlat, canonicalMPS, physicalToFlat
  , allPhysicalBasis )
import TensorNetwork.MPS.FinSupp3.Reference (mpsToFlatReference, mpoApplyFlatReference)
import TensorNetwork.MPS.FinSupp3.MPO (identityMPO, composeMPO, mpoApplyMPS, mpoApplyFlat)

smallComplex :: QC.Gen Field
smallComplex = do
  r <- QC.elements [-2 :: Int .. 2]
  i <- QC.elements [-2 :: Int .. 2]
  App.pure (fromIntegral r :+ fromIntegral i)

genCvp :: forall p. KnownNat p => QC.Gen (C p)
genCvp = do
  let n = fromIntegral (natVal (Proxy @p))
  xs <- replicateM n smallComplex
  App.pure $
    fromMaybe (error "genCvp") (create (LA.fromList xs))

genBond :: QC.Gen Bond
genBond = do
  len <- QC.choose (0, 3)
  FinSuppSeq App.<$> U.replicateM len smallComplex

genLeftSite :: forall p. KnownNat p => QC.Gen (LeftSite p)
genLeftSite = do
  n <- fromIntegral (natVal (Proxy @p))
  LeftSite . LinearMap App.<$> V.replicateM n genBond

genBulkSite :: forall p. KnownNat p => QC.Gen (BulkSite p)
genBulkSite = do
  chi <- QC.choose (0, 3)
  BulkSite . LinearMap App.<$> replicateM chi (Tensor App.<$> V.replicateM (fromIntegral (natVal (Proxy @p))) genBond)

genRightSite :: forall p. KnownNat p => QC.Gen (RightSite p)
genRightSite = do
  chi <- QC.choose (0, 3)
  RightSite . LinearMap App.<$> replicateM chi genCvp

genMPS :: forall p. KnownNat p => QC.Gen (MPS p)
genMPS = do
  l <- genLeftSite @p
  c <- genBulkSite @p
  r <- genRightSite @p
  App.pure (MPS l c r)

genOpLeft :: forall p. KnownNat p => QC.Gen (OpLeft p)
genOpLeft = do
  n <- fromIntegral (natVal (Proxy @p))
  chi <- QC.choose (0, 3)
  OpLeft . LinearMap App.<$> V.replicateM n (Tensor App.<$> replicateM chi genCvp)

genOpBulk :: forall p. KnownNat p => QC.Gen (OpBulk p)
genOpBulk = do
  chiIn <- QC.choose (0, 3)
  chiOut <- QC.choose (0, 3)
  OpBulk . LinearMap App.<$> replicateM chiIn (Tensor App.<$> replicateM chiOut genCvp)

genOpRight :: forall p. KnownNat p => QC.Gen (OpRight p)
genOpRight = do
  chi <- QC.choose (0, 3)
  OpRight . LinearMap App.<$> replicateM chi genCvp

genMPO :: forall p. KnownNat p => QC.Gen (MPO p)
genMPO = do
  l <- genOpLeft @p
  c <- genOpBulk @p
  r <- genOpRight @p
  App.pure (MPO l c r)

prop_addThenFlatten
  :: ( KnownNat p, KnownNat (PhysicalDim3 p) ) => MPS p -> MPS p -> QC.Property
prop_addThenFlatten m1 m2 =
  mpsToFlat (m1 ^+^ m2) QC.=== mpsToFlat m1 ^+^ mpsToFlat m2

prop_addThenFlattenVP2 :: QC.Property
prop_addThenFlattenVP2 =
  QC.forAll (genMPS @2) $ \m1 -> QC.forAll (genMPS @2) $ prop_addThenFlatten m1

prop_addThenFlattenVP3 :: QC.Property
prop_addThenFlattenVP3 =
  QC.forAll (genMPS @3) $ \m1 -> QC.forAll (genMPS @3) $ prop_addThenFlatten m1

prop_basisMPSMatchesPhysicalVP2 :: QC.Property
prop_basisMPSMatchesPhysicalVP2 =
  QC.forAll (QC.elements (allPhysicalBasis @2)) $ \b ->
    mpsToFlat (basisValue b :: MPS 2) QC.=== physicalToFlat (basisValue b :: Physical3 2)

prop_basisMPSMatchesPhysicalVP3 :: QC.Property
prop_basisMPSMatchesPhysicalVP3 =
  QC.forAll (QC.elements (allPhysicalBasis @3)) $ \b ->
    mpsToFlat (basisValue b :: MPS 3) QC.=== physicalToFlat (basisValue b :: Physical3 3)

prop_decomposePrimeMatchesPhysicalVP2 :: QC.Property
prop_decomposePrimeMatchesPhysicalVP2 =
  QC.forAll (genMPS @2) $ \m ->
    QC.forAll (QC.elements (allPhysicalBasis @2)) $ \b ->
      decompose' m b QC.=== decompose' (mpsToTensor m) b

prop_decomposePrimeMatchesPhysicalVP3 :: QC.Property
prop_decomposePrimeMatchesPhysicalVP3 =
  QC.forAll (genMPS @3) $ \m ->
    QC.forAll (QC.elements (allPhysicalBasis @3)) $ \b ->
      decompose' m b QC.=== decompose' (mpsToTensor m) b

prop_physicalRecomposeVP2 :: QC.Property
prop_physicalRecomposeVP2 =
  QC.forAll (genMPS @2) $ \m -> mpsToFlat (canonicalMPS @2 m) QC.=== mpsToFlat m

prop_physicalRecomposeVP3 :: QC.Property
prop_physicalRecomposeVP3 =
  QC.forAll (genMPS @3) $ \m -> mpsToFlat (canonicalMPS @3 m) QC.=== mpsToFlat m

prop_mpsFromFlatRoundTripVP2 :: QC.Property
prop_mpsFromFlatRoundTripVP2 =
  QC.forAll (genMPS @2) $ \m -> mpsToFlat (mpsFromFlat @2 (mpsToFlat m)) QC.=== mpsToFlat m

prop_mpsFromFlatRoundTripVP3 :: QC.Property
prop_mpsFromFlatRoundTripVP3 =
  QC.forAll (genMPS @3) $ \m -> mpsToFlat (mpsFromFlat @3 (mpsToFlat m)) QC.=== mpsToFlat m

prop_mpsToFlatMatchesReferenceVP2 :: QC.Property
prop_mpsToFlatMatchesReferenceVP2 =
  QC.forAll (genMPS @2) $ \m -> mpsToFlat m QC.=== mpsToFlatReference m

prop_mpsToFlatMatchesReferenceVP3 :: QC.Property
prop_mpsToFlatMatchesReferenceVP3 =
  QC.forAll (genMPS @3) $ \m -> mpsToFlat m QC.=== mpsToFlatReference m

prop_mpoApplyFlatMatchesReferenceVP2 :: QC.Property
prop_mpoApplyFlatMatchesReferenceVP2 =
  QC.forAll (genMPO @2) $ \h ->
    QC.forAll (genMPS @2) $ \m ->
      mpsToFlat (mpoApplyMPS h m) QC.=== mpoApplyFlatReference h (mpsToFlat m)

prop_composeMPOMatchesFlatVP2 :: QC.Property
prop_composeMPOMatchesFlatVP2 =
  QC.forAll (genMPO @2) $ \h1 ->
    QC.forAll (genMPO @2) $ \h2 ->
      QC.forAll (genMPS @2) $ \m ->
        mpsToFlat (mpoApplyMPS (composeMPO h1 h2) m)
          QC.=== mpoApplyFlat h1 (mpoApplyFlat h2 (mpsToFlat m))

prop_identityMPOVP2 :: QC.Property
prop_identityMPOVP2 =
  QC.forAll (genMPS @2) $ \m -> mpsToFlat (mpoApplyMPS (identityMPO @2) m) QC.=== mpsToFlat m
