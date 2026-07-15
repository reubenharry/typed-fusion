{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

module TensorNetwork.MPS.FinSupp.Properties where

import Data.Complex (Complex ((:+)))
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import GHC.TypeLits (KnownNat, natVal, type (*))
import qualified Control.Arrow.Constrained as AC
import Math.LinearMap.Category (LinearMap (..), Tensor (..), getLinearMap, (⊗))
import Math.LinearMap.Category.Instances ()
import Numeric.LinearAlgebra.Static (C, Sized (create))
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import qualified Numeric.LinearAlgebra as LA
import Data.VectorSpace.Free.FiniteSupportedSequence (FinSuppSeq (..))
import qualified Test.QuickCheck as QC
import qualified Control.Applicative as App
import Control.Monad (replicateM)
import Data.Basis (HasBasis (basisValue), decompose')
import Data.Finite (finites)
import Data.VectorSpace (AdditiveGroup ((^+^)))
import TensorNetwork.MPS.FinSupp.Internal
-- import TensorNetwork.MPS.FinSupp.Contraction
  -- ()

import TensorNetwork.MPS.FinSupp.Physical
import TensorNetwork.MPS.FinSupp.Bond (bondCoeff, Bond)
import TensorNetwork.MPS.FinSupp.MPO 
import Math.TensorNetwork (Field)
import TensorNetwork.MPS.General (LeftSite, BulkSite, RightSite)



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

-- genLeftSite :: forall p. KnownNat p => QC.Gen (LeftSite p)
-- genLeftSite = do
--   let n = fromIntegral (natVal (Proxy @p))
--   LeftSite . LinearMap App.<$> V.replicateM n genBond

-- genBulkSite :: forall p. KnownNat p => QC.Gen (BulkSite p)
-- genBulkSite = do
--   chi <- QC.choose (0, 3)
--   BulkSite . LinearMap App.<$> replicateM chi (Tensor App.<$> V.replicateM (fromIntegral (natVal (Proxy @p))) genBond)

-- genRightSite :: forall p. KnownNat p => QC.Gen (RightSite p)
-- genRightSite = do
--   chi <- QC.choose (0, 3)
--   RightSite . LinearMap App.<$> replicateM chi genCvp

-- genMPS :: forall p. KnownNat p => QC.Gen (MPS p)
-- genMPS = do
--   l <- genLeftSite @p
--   c <- genBulkSite @p
--   r <- genRightSite @p
--   App.pure (MPS l c r)

-- genOpLeft :: forall p. KnownNat p => QC.Gen (OpLeft p)
-- genOpLeft = do
--   let n = fromIntegral (natVal (Proxy @p))
--   chi <- QC.choose (0, 3)
--   OpLeft . LinearMap App.<$> V.replicateM n (Tensor App.<$> replicateM chi genCvp)

-- genOpBulk :: forall p. KnownNat p => QC.Gen (OpBulk p)
-- genOpBulk = do
--   chiIn <- QC.choose (0, 3)
--   chiOut <- QC.choose (0, 3)
--   OpBulk . LinearMap App.<$> replicateM chiIn (Tensor App.<$> replicateM chiOut genCvp)

-- genOpRight :: forall p. KnownNat p => QC.Gen (OpRight p)
-- genOpRight = do
--   chi <- QC.choose (0, 3)
--   OpRight . LinearMap App.<$> replicateM chi genCvp

-- genMPO :: forall p. KnownNat p => QC.Gen (MPO p)
-- genMPO = do
--   l <- genOpLeft @p
--   c <- genOpBulk @p
--   r <- genOpRight @p
--   App.pure (MPO l c r)

-- bondCoeffsMatch :: Bond -> Bond -> Bool
-- bondCoeffsMatch a b =
--   let len = max (bondActiveLen a) (bondActiveLen b)
--   in all (\i -> bondCoeff a i == bondCoeff b i) [0 .. len - 1]

-- bondActiveLen :: Bond -> Int
-- bondActiveLen (FinSuppSeq v) =
--   if U.null v then 0 else go (U.length v - 1)
--   where
--     go i
--       | i < 0        = 0
--       | v U.! i /= 0 = i + 1
--       | otherwise    = go (i - 1)

-- prop_amplitudeMatchesDecomposeVP2 :: QC.Property
-- prop_amplitudeMatchesDecomposeVP2 =
--   QC.forAll (genMPS @2) $ \m ->
--     QC.conjoin
--       [ amplitude m s1 s2 s3
--           QC.=== decompose' (mpsToTensor m)
--                (finites @2 !! s1, (finites @2 !! s2, finites @2 !! s3))
--       | s1 <- [0 .. 1], s2 <- [0 .. 1], s3 <- [0 .. 1]
--       ]

-- prop_amplitudeEncodeVP2 :: QC.Property
-- prop_amplitudeEncodeVP2 =
--   QC.forAll (genMPS @2) $ \m ->
--     let t = mpsToTensor m
--         m' = mpsFromPhysical t
--     in QC.conjoin
--          [ amplitude m' s1 s2 s3 QC.=== amplitude m s1 s2 s3
--          | s1 <- [0 .. 1], s2 <- [0 .. 1], s3 <- [0 .. 1]
--          ]

-- prop_tensorEncodeVP2 :: QC.Property
-- prop_tensorEncodeVP2 =
--   QC.forAll (genMPS @2) $ \m ->
--     physicalToFlat (mpsToTensor (mpsFromPhysical (mpsToTensor m)))
--       QC.=== physicalToFlat (mpsToTensor (m :: MPS 2))

-- prop_addThenFlatten
--   :: ( KnownNat p, KnownNat (PhysicalDim3 p), KnownNat (p * p) )
--   => MPS p -> MPS p -> QC.Property
-- prop_addThenFlatten m1 m2 =
--   mpsToFlat (m1 ^+^ m2) QC.=== mpsToFlat m1 ^+^ mpsToFlat m2

-- prop_addThenFlattenVP2 :: QC.Property
-- prop_addThenFlattenVP2 =
--   QC.forAll (genMPS @2) $ \m1 -> QC.forAll (genMPS @2) $ prop_addThenFlatten m1

-- prop_addThenFlattenVP3 :: QC.Property
-- prop_addThenFlattenVP3 =
--   QC.forAll (genMPS @3) $ \m1 -> QC.forAll (genMPS @3) $ prop_addThenFlatten m1

-- prop_basisMPSMatchesPhysicalVP2 :: QC.Property
-- prop_basisMPSMatchesPhysicalVP2 =
--   QC.forAll (QC.elements (allPhysicalBasis @2)) $ \b ->
--     mpsToFlat (basisValue b :: MPS 2) QC.=== physicalToFlat (basisValue b :: Physical3 2)

-- prop_basisMPSMatchesPhysicalVP3 :: QC.Property
-- prop_basisMPSMatchesPhysicalVP3 =
--   QC.forAll (QC.elements (allPhysicalBasis @3)) $ \b ->
--     mpsToFlat (basisValue b :: MPS 3) QC.=== physicalToFlat (basisValue b :: Physical3 3)

-- prop_decomposePrimeMatchesPhysicalVP2 :: QC.Property
-- prop_decomposePrimeMatchesPhysicalVP2 =
--   QC.forAll (genMPS @2) $ \m ->
--     QC.forAll (QC.elements (allPhysicalBasis @2)) $ \b ->
--       decompose' m b QC.=== decompose' (mpsToTensor m) b

-- prop_decomposePrimeMatchesPhysicalVP3 :: QC.Property
-- prop_decomposePrimeMatchesPhysicalVP3 =
--   QC.forAll (genMPS @3) $ \m ->
--     QC.forAll (QC.elements (allPhysicalBasis @3)) $ \b ->
--       decompose' m b QC.=== decompose' (mpsToTensor m) b

-- prop_physicalRecomposeVP2 :: QC.Property
-- prop_physicalRecomposeVP2 =
--   QC.forAll (genMPS @2) $ \m -> mpsToFlat (canonicalMPS @2 m) QC.=== mpsToFlat m

-- prop_physicalRecomposeVP3 :: QC.Property
-- prop_physicalRecomposeVP3 =
--   QC.forAll (genMPS @3) $ \m -> mpsToFlat (canonicalMPS @3 m) QC.=== mpsToFlat m

-- prop_mpsFromFlatRoundTripVP2 :: QC.Property
-- prop_mpsFromFlatRoundTripVP2 =
--   QC.forAll (genMPS @2) $ \m -> mpsToFlat (mpsFromFlat @2 (mpsToFlat m)) QC.=== mpsToFlat m

-- prop_mpsFromFlatRoundTripVP3 :: QC.Property
-- prop_mpsFromFlatRoundTripVP3 =
--   QC.forAll (genMPS @3) $ \m -> mpsToFlat (mpsFromFlat @3 (mpsToFlat m)) QC.=== mpsToFlat m

-- prop_mpsToFlatMatchesReferenceVP2 :: QC.Property
-- prop_mpsToFlatMatchesReferenceVP2 =
--   QC.forAll (genMPS @2) $ \m -> mpsToFlat m QC.=== mpsToFlatReference m

-- prop_mpsToFlatMatchesReferenceVP3 :: QC.Property
-- prop_mpsToFlatMatchesReferenceVP3 =
--   QC.forAll (genMPS @3) $ \m -> mpsToFlat m QC.=== mpsToFlatReference m

-- prop_leftTransferMatchesReferenceVP2 :: QC.Property
-- prop_leftTransferMatchesReferenceVP2 =
--   QC.forAll (genLeftSite @2) $ \site ->
--   QC.forAll (QC.choose (0, 1)) $ \s ->
--     bondCoeffsMatch (leftTransfer site AC.$ (one1 ⊗ basisCvp @2 s)) (applyLeftSite site s)

-- prop_bulkTransferMatchesReferenceVP2 :: QC.Property
-- prop_bulkTransferMatchesReferenceVP2 =
--   QC.forAll (genBulkSite @2) $ \site ->
--   QC.forAll genBond $ \bond ->
--   QC.forAll (QC.choose (0, 1)) $ \s ->
--     bondCoeffsMatch (bulkTransfer site AC.$ (bond ⊗ basisCvp @2 s)) (applyBulkSite site bond s)

-- prop_rightTransferMatchesReferenceVP2 :: QC.Property
-- prop_rightTransferMatchesReferenceVP2 =
--   QC.forAll (genRightSite @2) $ \site ->
--   QC.forAll genBond $ \bond ->
--   QC.forAll (QC.choose (0, 1)) $ \s ->
--     cvpCoeff (rightTransfer site AC.$ (bond ⊗ basisCvp @2 s)) 0
--       QC.=== applyRightSite site bond s

-- prop_mpoApplyFlatMatchesReferenceVP2 :: QC.Property
-- prop_mpoApplyFlatMatchesReferenceVP2 =
--   QC.forAll (genMPO @2) $ \h ->
--     QC.forAll (genMPS @2) $ \m ->
--       mpsToFlat (mpoApplyMPS h m) QC.=== mpoApplyFlatReference h (mpsToFlat m)

-- prop_composeMPOMatchesFlatVP2 :: QC.Property
-- prop_composeMPOMatchesFlatVP2 =
--   QC.forAll (genMPO @2) $ \h1 ->
--     QC.forAll (genMPO @2) $ \h2 ->
--       QC.forAll (genMPS @2) $ \m ->
--         mpsToFlat (mpoApplyMPS (composeMPO h1 h2) m)
--           QC.=== mpoApplyFlat h1 (mpoApplyFlat h2 (mpsToFlat m))

-- allIndexTriples :: [Int] -> [(Int, Int, Int)]
-- allIndexTriples ix = [(i, j, k) | i <- ix, j <- ix, k <- ix]

-- allIndexSextuples :: [Int] -> [(Int, Int, Int, Int, Int, Int)]
-- allIndexSextuples ix =
--   [ (t1, t2, t3, s1, s2, s3)
--   | t1 <- ix, t2 <- ix, t3 <- ix, s1 <- ix, s2 <- ix, s3 <- ix
--   ]

-- composedMPOElement
--   :: MPO 2 -> MPO 2 -> Int -> Int -> Int -> Int -> Int -> Int -> Field
-- composedMPOElement h1 h2 t1 t2 t3 s1 s2 s3 =
--   sum
--     [ mpoElement h1 t1 t2 t3 u1 u2 u3
--         * mpoElement h2 u1 u2 u3 s1 s2 s3
--     | u1 <- [0, 1], u2 <- [0, 1], u3 <- [0, 1]
--     ]

-- prop_composeMPOElementMatchesSumVP2 :: QC.Property
-- prop_composeMPOElementMatchesSumVP2 =
--   QC.forAll (genMPO @2) $ \h1 ->
--     QC.forAll (genMPO @2) $ \h2 ->
--       QC.conjoin
--         [ mpoElement (composeMPO h1 h2) t1 t2 t3 s1 s2 s3
--             QC.=== composedMPOElement h1 h2 t1 t2 t3 s1 s2 s3
--         | (t1, t2, t3, s1, s2, s3) <- allIndexSextuples [0, 1]
--         ]

-- genSparseMPOTerms :: QC.Gen [((Int, Int, Int, Int, Int, Int), Field)]
-- genSparseMPOTerms = do
--   n <- QC.choose (1, 6)
--   replicateM n $ do
--     t1 <- QC.elements [0, 1]
--     t2 <- QC.elements [0, 1]
--     t3 <- QC.elements [0, 1]
--     s1 <- QC.elements [0, 1]
--     s2 <- QC.elements [0, 1]
--     s3 <- QC.elements [0, 1]
--     c <- smallComplex
--     App.pure ((t1, t2, t3, s1, s2, s3), c)

-- sparseMPOElementFromTerms
--   :: [((Int, Int, Int, Int, Int, Int), Field)]
--   -> Int -> Int -> Int -> Int -> Int -> Int -> Field
-- sparseMPOElementFromTerms terms t1 t2 t3 s1 s2 s3 =
--   sum
--     [ c
--     | ((a, b, c', d, e, f), c) <- terms
--     , a == t1, b == t2, c' == t3, d == s1, e == s2, f == s3
--     ]

-- prop_mpoFromElementRoundTripVP2 :: QC.Property
-- prop_mpoFromElementRoundTripVP2 =
--   QC.forAll genSparseMPOTerms $ \terms ->
--     let f = sparseMPOElementFromTerms terms
--         h = mpoFromElement @2 f
--     in QC.conjoin
--          [ mpoElement h t1 t2 t3 s1 s2 s3 QC.=== f t1 t2 t3 s1 s2 s3
--          | (t1, t2, t3, s1, s2, s3) <- allIndexSextuples [0, 1]
--          ]

-- prop_identityMPOVP2 :: QC.Property
-- prop_identityMPOVP2 =
--   QC.forAll (genMPS @2) $ \m -> mpsToFlat (mpoApplyMPS (identityMPO @2) m) QC.=== mpsToFlat m

-- prop_identityMPOElementsVP2 :: QC.Property
-- prop_identityMPOElementsVP2 =
--   QC.conjoin
--     [ mpoElement (identityMPO @2) t1 t2 t3 s1 s2 s3
--         QC.=== (if t1 == s1 && t2 == s2 && t3 == s3 then 1 else 0)
--     | (t1, t2, t3, s1, s2, s3) <- allIndexSextuples [0, 1]
--     ]
