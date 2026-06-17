{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module TensorNetwork.MPS.FinSupp3 where

import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import Data.VectorSpace.Free.FiniteSupportedSequence
import Data.Basis (HasBasis (..))
import Data.Finite (Finite, finites, getFinite)
import Data.Complex (Complex ((:+)))
import Data.Proxy (Proxy (..))
import Data.Coerce (coerce)
import Data.List (foldl', intercalate)
import Data.Maybe (fromMaybe)
import GHC.TypeLits (KnownNat, natVal, type (*))
import Data.VectorSpace (sumV)
import qualified Test.QuickCheck as QC
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)
import Math.LinearMap.Category
  ( type (+>), type (⊗), LinearMap (..), Tensor (..),
    AdditiveGroup (..), VectorSpace (..), Scalar, getLinearMap, getTensorProduct )
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Instances.Deriving ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Prelude hiding ((.), ($))
import Control.Monad (replicateM)
import qualified Control.Applicative as App
import Control.Category.Constrained.Prelude
import Numeric.LinearAlgebra.Static (C, M, Sized (..), create, extract, fromList)
import qualified Numeric.LinearAlgebra as LA

type Field = Complex Double
type Bond = FinSuppSeq Field

-- | Three-site physical Hilbert space @VP ⊗ VP ⊗ VP@ (left-associated).
type Physical3 vp = (C vp ⊗ C vp) ⊗ C vp

-- | Flattened dimension @vp³@ for the physical space above.
type PhysicalDim3 vp = vp * vp * vp

-- | Active support length of a bond vector (trailing zeros trimmed).
activeDimBond :: Bond -> Int
activeDimBond (FinSuppSeq v)
  | U.null v  = 0
  | otherwise = 1 + go (U.length v - 1)
  where
    go i
      | i < 0        = 0
      | v U.! i /= 0 = i + 1
      | otherwise    = go (i - 1)

-- | Shift bond-vector support right by @n@ slots (prepend zeros).
offsetBond :: Int -> Bond -> Bond
offsetBond 0 b = b
offsetBond n (FinSuppSeq v)
  | n <= 0    = FinSuppSeq v
  | otherwise = FinSuppSeq (U.replicate n 0 U.++ v)

type BondVec = V.Vector Bond

activeDimIntoBond :: BondVec -> Int
activeDimIntoBond = V.foldl' max 0 . V.map activeDimBond

offsetBondVec :: Int -> BondVec -> BondVec
offsetBondVec n = V.map (offsetBond n)

-- | Block-embed the second map's bond *output* after the first map's active dimension.
offsetCodomainIntoBond
  :: Int -> (C vp +> Bond) -> (C vp +> Bond)
offsetCodomainIntoBond n (LinearMap imgs) =
  LinearMap (offsetBondVec n imgs)

isZeroBond :: Bond -> Bool
isZeroBond (FinSuppSeq v) = U.all (== 0) v

activeDimCenterSite :: forall vp. KnownNat vp => [C vp ⊗ Bond] -> Int
activeDimCenterSite imgs =
  foldl'
    (\acc (i, Tensor rows) ->
       if V.any (not . isZeroBond) rows then i + 1 else acc)
    0
    (zip [0 ..] imgs)

activeDimCenterOut :: [C vp ⊗ Bond] -> Int
activeDimCenterOut imgs =
  maximum $
    0 :
      [ activeDimBond row
      | Tensor rows <- imgs
      , row <- V.toList rows
      ]

activeDimRightSite :: forall vp. KnownNat vp => [C vp] -> Int
activeDimRightSite imgs =
  foldl' (\acc (i, v) -> if v == zeroV then acc else i + 1) 0 (zip [0 ..] imgs)

padLinearMapDomain :: AdditiveGroup w => Int -> [w] -> [w]
padLinearMapDomain chi imgs =
  take chi (imgs ++ replicate (max 0 (chi - length imgs)) zeroV)

padCenterDomain
  :: forall vp. KnownNat vp => Int -> (Bond +> (C vp ⊗ Bond)) -> (Bond +> (C vp ⊗ Bond))
padCenterDomain chi (LinearMap imgs) =
  LinearMap (padLinearMapDomain chi imgs)

padRightDomain
  :: forall vp. KnownNat vp => Int -> (Bond +> C vp) -> (Bond +> C vp)
padRightDomain chi (LinearMap imgs) =
  LinearMap (padLinearMapDomain chi imgs)

bondDimMPS :: forall vp. KnownNat vp => MPS vp -> Int
bondDimMPS (MPS l c r) =
  maximum
    [ activeDimIntoBond (getLinearMap l)
    , activeDimCenterSite (getLinearMap c)
    , activeDimCenterOut (getLinearMap c)
    , activeDimRightSite (getLinearMap r)
    ]

-- | Offset the bond leg inside a physical ⊗ bond tensor.
offsetBondInTensor
  :: Int -> (C vp ⊗ Bond) -> (C vp ⊗ Bond)
offsetBondInTensor n (Tensor tp) = Tensor (V.map (offsetBond n) tp)

addIntoBond
  :: KnownNat vp => Int -> (C vp +> Bond) -> (C vp +> Bond) -> (C vp +> Bond)
addIntoBond chiF f g = f ^+^ offsetCodomainIntoBond chiF g

data MPS vp = MPS
  { leftMPS  :: C vp +> Bond
  , center         :: Bond +> (C vp ⊗ Bond)
  , rightMPS :: Bond +> C vp
  }

instance KnownNat vp => Show (MPS vp) where
  show _ = "MPS"

zeroMPS :: KnownNat vp => MPS vp
zeroMPS = MPS zeroV zeroV zeroV

addMPS
  :: KnownNat vp => MPS vp -> MPS vp -> MPS vp
addMPS m1 m2 =
  let chi1 = bondDimMPS m1
      chi2 = bondDimMPS m2
      MPS l1 c1 r1 = m1
      MPS l2 c2 r2 = m2
      c1' = padCenterDomain chi1 c1
      c2' = padCenterDomain chi2 c2
      r1' = padRightDomain chi1 r1
      r2' = padRightDomain chi2 r2
  in MPS
       (addIntoBond chi1 l1 l2)
       (LinearMap $
          getLinearMap c1'
            ++ map (offsetBondInTensor chi1) (getLinearMap c2'))
       (LinearMap $ getLinearMap r1' ++ getLinearMap r2')

scaleMPS :: KnownNat vp => Field -> MPS vp -> MPS vp
scaleMPS μ (MPS l c r) =
  MPS (μ *^ l) (μ *^ c) (μ *^ r)

instance KnownNat vp => AdditiveGroup (MPS vp) where
  zeroV = zeroMPS
  (^+^) = addMPS
  negateV m = scaleMPS (-1) m

instance KnownNat vp => VectorSpace (MPS vp) where
  type Scalar (MPS vp) = Field
  μ *^ m = scaleMPS μ m

{-# DEPRECATED addClever "Use (^+^) on MPS instead" #-}
addClever :: KnownNat vp => MPS vp -> MPS vp -> MPS vp
addClever = addMPS

-- | Stack @vp@ column vectors into an @M vp vp@ (one row per physical index).
matFromCVpRows :: forall vp. KnownNat vp => V.Vector (C vp) -> M vp vp
matFromCVpRows cols =
  fromMaybe (error "matFromCVpRows: create failed") $
    create (LA.fromRows (map extract (V.toList cols)))

-- | Contract the bond leg of one center-site tensor against @Bond +> C vp@.
contractSiteTensor
  :: forall vp
   . KnownNat vp
  => (Bond +> C vp) -> (C vp ⊗ Bond) -> (C vp ⊗ C vp)
contractSiteTensor right (Tensor rows) =
  Tensor (matFromCVpRows (V.map (right $) rows))

-- | Contract center ⊗ right on the bond leg.
contractCenterRight
  :: forall vp
   . KnownNat vp
  => (Bond +> (C vp ⊗ Bond)) -> (Bond +> C vp) -> Bond +> (C vp ⊗ C vp)
contractCenterRight (LinearMap centerImgs) right =
  LinearMap (map (contractSiteTensor right) centerImgs)

flattenBody2 :: forall vp. KnownNat vp => (C vp ⊗ C vp) -> LA.Vector Field
flattenBody2 (Tensor m) = LA.flatten (extract m)

-- | Fully contracted map @C vp +> (C vp ⊗ C vp)@.
--
-- Amplitude for @(s₁, s₂, s₃)@ is the @(s₂, s₃)@ component of @(stateMap mps) e_{s₁}@.
stateMap
  :: forall vp
   . (KnownNat vp, KnownNat (vp * vp))
  => MPS vp -> C vp +> (C vp ⊗ C vp)
stateMap (MPS (LinearMap leftImgs) centerSite right) =
  let contracted = V.map (contractCenterRight centerSite right $) leftImgs
      rows = map (LA.toList . flattenBody2) (V.toList contracted)
      mat = LA.fromRows (map LA.fromList rows)
  in LinearMap (fromMaybe (error "stateMap: create failed") (create mat))

-- | Alias for 'stateMap' emphasizing the linear-map viewpoint.
mpsStateMap
  :: (KnownNat vp, KnownNat (vp * vp)) => MPS vp -> C vp +> (C vp ⊗ C vp)
mpsStateMap = stateMap

-- | The state tensor in @VP ⊗ (VP ⊗ VP)@ (right-associated triple product).
mpsToTensorNested
  :: forall vp
   . (KnownNat vp, KnownNat (vp * vp))
  => MPS vp -> C vp ⊗ (C vp ⊗ C vp)
mpsToTensorNested mps = coerce (stateMap mps)

-- | The state vector in @VP ⊗ VP ⊗ VP@, i.e. @(VP ⊗ VP) ⊗ VP@.
--
-- Shares the same matrix storage as 'mpsToTensorNested'; index ordering in the
-- flat vector is @(s₁, s₂, s₃) ↦ (s₁·vp + s₂)·vp + s₃@.
mpsToPhysical3
  :: forall vp
   . (KnownNat vp, KnownNat (vp * vp))
  => MPS vp -> Physical3 vp
mpsToPhysical3 mps =
  Tensor (getTensorProduct (mpsToTensorNested mps))

-- | Same state as a flat @C (vp³)@ column vector.
mpsToFlat
  :: forall vp
   . (KnownNat vp, KnownNat (vp * vp), KnownNat (PhysicalDim3 vp))
  => MPS vp -> C (PhysicalDim3 vp)
mpsToFlat mps =
  fromMaybe (error "mpsToFlat: create failed") $
    create (LA.flatten (extract (getTensorProduct (mpsToPhysical3 mps))))

vpDim :: forall vp. KnownNat vp => Int
vpDim = fromIntegral (natVal (Proxy @vp))

unitBond :: Bond
unitBond = FinSuppSeq (U.fromList [1])

basisCvp :: forall vp. KnownNat vp => Int -> C vp
basisCvp i = fromList [ if j == i then 1 else 0 | j <- [0 .. vpDim @vp - 1] ]

-- | Decode a flat physical index @k@ to @(s₁, s₂, s₃)@ matching 'mpsToFlat'.
physicalIndices :: Int -> Int -> (Int, Int, Int)
physicalIndices vp k =
  let s3 = k `mod` vp
      t  = k `div` vp
      s2 = t `mod` vp
      s1 = t `div` vp
  in (s1, s2, s3)

-- | Flatten a physical tensor to @C (vp³)@ (same index order as 'mpsToFlat').
physicalToFlat
  :: forall vp
   . (KnownNat vp, KnownNat (vp * vp), KnownNat (PhysicalDim3 vp))
  => Physical3 vp -> C (PhysicalDim3 vp)
physicalToFlat phys =
  fromMaybe (error "physicalToFlat: create failed") $
    create (LA.flatten (extract (getTensorProduct phys)))

-- | Flat @C (vp³)@ index of a 'Physical3' basis vector (linearmap storage order).
basisFlatIndex
  :: forall vp
   . (KnownNat vp, KnownNat (vp * vp), KnownNat (PhysicalDim3 vp))
  => Basis (Physical3 vp)
  -> Int
basisFlatIndex b =
  let flat = physicalToFlat (basisValue b :: Physical3 vp)
  in fromIntegral $
       getFinite $
         head [b' | (b', c) <- decompose @(C (PhysicalDim3 vp)) flat, c == 1]

-- | Nested 'Basis (Physical3 vp)' label as site indices (via flat index).
physicalIndicesFromBasis
  :: forall vp
   . (KnownNat vp, KnownNat (vp * vp), KnownNat (PhysicalDim3 vp))
  => Basis (Physical3 vp)
  -> (Int, Int, Int)
physicalIndicesFromBasis b =
  physicalIndices (vpDim @vp) (basisFlatIndex @vp b)

flatBasisToPhysicalBasis
  :: forall vp
   . (KnownNat vp, KnownNat (vp * vp), KnownNat (PhysicalDim3 vp))
  => Finite (PhysicalDim3 vp)
  -> Basis (Physical3 vp)
flatBasisToPhysicalBasis b =
  head
    [ bPhys
    | bPhys <- allPhysicalBasis @vp
    , basisFlatIndex bPhys == fromIntegral (getFinite b)
    ]

allPhysicalBasis :: forall vp. KnownNat vp => [Basis (Physical3 vp)]
allPhysicalBasis =
  [ ((b1, b2), b3)
  | b1 <- finites @vp
  , b2 <- finites @vp
  , b3 <- finites @vp
  ]

-- | Product state @|s₁,s₂,s₃⟩@ as a bond-dimension-1 MPS.
productMPSAtIndices
  :: forall vp
   . (KnownNat vp, KnownNat (vp * vp), KnownNat (PhysicalDim3 vp))
  => Int -> Int -> Int -> MPS vp
productMPSAtIndices s1 s2 s3 =
  let vp = vpDim @vp
      leftRows = V.generate vp (\j -> if j == s1 then unitBond else zeroV)
      centerRows = V.generate vp (\j -> if j == s2 then unitBond else zeroV)
  in MPS
       (LinearMap leftRows)
       (LinearMap [Tensor centerRows])
       (LinearMap [basisCvp @vp s3])

-- | Product state for a 'Physical3' basis label.
productMPSFromBasis
  :: forall vp
   . (KnownNat vp, KnownNat (vp * vp), KnownNat (PhysicalDim3 vp))
  => Basis (Physical3 vp) -> MPS vp
productMPSFromBasis b =
  let (s1, s2, s3) = physicalIndicesFromBasis b
  in productMPSAtIndices s1 s2 s3

-- | Canonical MPS section for a physical tensor.
--
-- Built in one pass from the physical coefficients (one bond index per
-- nonzero term), so @mpsFromPhysical@ round-trips with 'mpsToPhysical3'.
mpsFromPhysical
  :: forall vp
   . (KnownNat vp, KnownNat (vp * vp), KnownNat (PhysicalDim3 vp))
  => Physical3 vp -> MPS vp
mpsFromPhysical phys =
  let vp = vpDim @vp
      terms =
        [ (physicalIndicesFromBasis b, c)
        | (b, c) <- decompose phys
        , c /= 0
        ]
  in case terms of
       [] -> zeroMPS
       _  ->
         MPS
           (LinearMap (mpsLeftRows vp terms))
           (LinearMap (mpsCenterImgs vp terms))
           (LinearMap (mpsRightImgs terms))

mpsLeftRows :: Int -> [((Int, Int, Int), Field)] -> BondVec
mpsLeftRows vp terms =
  V.generate vp $ \s1 ->
    FinSuppSeq $
      U.fromList [ if s1 == s1' then c else 0 | ((s1', _, _), c) <- terms ]

mpsCenterImgs :: Int -> [((Int, Int, Int), Field)] -> [C vp ⊗ Bond]
mpsCenterImgs vp terms =
  [ Tensor (V.generate vp $ \p -> if p == s2 then offsetBond i unitBond else zeroV)
  | (i, ((_, s2, _), _)) <- zip [0 ..] terms
  ]

mpsRightImgs :: forall vp. KnownNat vp => [((Int, Int, Int), Field)] -> [C vp]
mpsRightImgs terms = [ basisCvp @vp s3 | ((_, _, s3), _) <- terms ]

instance
  ( KnownNat vp
  , KnownNat (vp * vp)
  , KnownNat (PhysicalDim3 vp)
  ) =>
  HasBasis (MPS vp)
  where
  type Basis (MPS vp) = Basis (Physical3 vp)
  basisValue b = mpsFromPhysical (basisValue b :: Physical3 vp)
  decompose m = decompose (mpsToPhysical3 m)
  decompose' m = decompose' (mpsToPhysical3 m)

-- | Canonical MPS section for a flat @C (vp³)@ vector.
mpsFromFlat
  :: forall vp
   . (KnownNat vp, KnownNat (vp * vp), KnownNat (PhysicalDim3 vp))
  => C (PhysicalDim3 vp) -> MPS vp
mpsFromFlat = mpsFromPhysical . physicalFromFlat

physicalFromFlat
  :: forall vp
   . (KnownNat vp, KnownNat (vp * vp), KnownNat (PhysicalDim3 vp))
  => C (PhysicalDim3 vp) -> Physical3 vp
physicalFromFlat v =
  sumV
    [ c *^ (basisValue (flatBasisToPhysicalBasis b) :: Physical3 vp)
    | (b, c) <- decompose @(C (PhysicalDim3 vp)) v
    , c /= 0
    ]

-- | Reconstruct an MPS from its physical basis decomposition.
--
-- Round-trips with 'decompose' on physical space: @mpsToPhysical3 . canonicalMPS =
-- mpsToPhysical3@.
canonicalMPS :: (KnownNat vp, KnownNat (vp * vp), KnownNat (PhysicalDim3 vp)) => MPS vp -> MPS vp
canonicalMPS = mpsFromPhysical . mpsToPhysical3

-- | Small integer complexes for exact QuickCheck properties.
smallComplex :: QC.Gen Field
smallComplex = do
  r <- QC.elements [-2 :: Int .. 2]
  i <- QC.elements [-2 :: Int .. 2]
  App.pure (fromIntegral r :+ fromIntegral i)

genCvp :: forall vp. KnownNat vp => QC.Gen (C vp)
genCvp = do
  let n = fromIntegral (natVal (Proxy @vp))
  xs <- replicateM n smallComplex
  App.pure $
    fromMaybe (error "genCvp: create failed") (create (LA.fromList xs))

genBond :: QC.Gen Bond
genBond = do
  len <- QC.choose (0, 3)
  FinSuppSeq App.<$> U.replicateM len smallComplex

genBondDomainMap :: QC.Gen w -> QC.Gen (Bond +> w)
genBondDomainMap wGen = do
  chi <- QC.choose (0, 3)
  LinearMap App.<$> replicateM chi wGen

-- | Random MPS with bond rank up to @3@ (used by tests).
genMPS :: forall vp. KnownNat vp => QC.Gen (MPS vp)
genMPS = do
  let n = fromIntegral (natVal (Proxy @vp))
  left <- LinearMap App.<$> V.replicateM n genBond
  centerSite <- genBondDomainMap (Tensor App.<$> V.replicateM n genBond)
  right <- genBondDomainMap genCvp
  App.pure (MPS left centerSite right)

-- | Addition in MPS form agrees with addition in flattened physical space.
prop_addThenFlatten
  :: ( KnownNat vp
     , KnownNat (vp * vp)
     , KnownNat (vp * vp * vp)
     )
  => MPS vp -> MPS vp -> QC.Property
prop_addThenFlatten m1 m2 =
  mpsToFlat (m1 ^+^ m2) QC.=== mpsToFlat m1 ^+^ mpsToFlat m2

prop_addThenFlattenVP2 :: QC.Property
prop_addThenFlattenVP2 =
  QC.forAll (genMPS @2) $ \m1 ->
    QC.forAll (genMPS @2) $ \m2 ->
      prop_addThenFlatten m1 m2

prop_addThenFlattenVP3 :: QC.Property
prop_addThenFlattenVP3 =
  QC.forAll (genMPS @3) $ \m1 ->
    QC.forAll (genMPS @3) $ \m2 ->
      prop_addThenFlatten m1 m2

prop_basisMPSMatchesPhysicalVP2 :: QC.Property
prop_basisMPSMatchesPhysicalVP2 =
  QC.forAll (QC.elements allPhysicalBasis2) $ \b ->
    mpsToFlat (basisValue b :: MPS 2)
      QC.=== physicalToFlat (basisValue b :: Physical3 2)

prop_basisMPSMatchesPhysicalVP3 :: QC.Property
prop_basisMPSMatchesPhysicalVP3 =
  QC.forAll (QC.elements allPhysicalBasis3) $ \b ->
    mpsToFlat (basisValue b :: MPS 3)
      QC.=== physicalToFlat (basisValue b :: Physical3 3)

prop_decomposePrimeMatchesPhysicalVP2 :: QC.Property
prop_decomposePrimeMatchesPhysicalVP2 =
  QC.forAll (genMPS @2) $ \(m :: MPS 2) ->
    QC.forAll (QC.elements allPhysicalBasis2) $ \b ->
      decompose' m b QC.=== decompose' (mpsToPhysical3 m) b

prop_decomposePrimeMatchesPhysicalVP3 :: QC.Property
prop_decomposePrimeMatchesPhysicalVP3 =
  QC.forAll (genMPS @3) $ \(m :: MPS 3) ->
    QC.forAll (QC.elements allPhysicalBasis3) $ \b ->
      decompose' m b QC.=== decompose' (mpsToPhysical3 m) b

allPhysicalBasis2 :: [Basis (Physical3 2)]
allPhysicalBasis2 = allPhysicalBasis @2

allPhysicalBasis3 :: [Basis (Physical3 3)]
allPhysicalBasis3 = allPhysicalBasis @3

prop_physicalRecomposeVP2 :: QC.Property
prop_physicalRecomposeVP2 =
  QC.forAll (genMPS @2) $ \(m :: MPS 2) ->
    mpsToFlat (canonicalMPS @2 m) QC.=== mpsToFlat m

prop_physicalRecomposeVP3 :: QC.Property
prop_physicalRecomposeVP3 =
  QC.forAll (genMPS @3) $ \(m :: MPS 3) ->
    mpsToFlat (canonicalMPS @3 m) QC.=== mpsToFlat m

prop_mpsFromFlatRoundTripVP2 :: QC.Property
prop_mpsFromFlatRoundTripVP2 =
  QC.forAll (genMPS @2) $ \(m :: MPS 2) ->
    mpsToFlat (mpsFromFlat @2 (mpsToFlat m)) QC.=== mpsToFlat m

prop_mpsFromFlatRoundTripVP3 :: QC.Property
prop_mpsFromFlatRoundTripVP3 =
  QC.forAll (genMPS @3) $ \(m :: MPS 3) ->
    mpsToFlat (mpsFromFlat @3 (mpsToFlat m)) QC.=== mpsToFlat m

runAddThenFlattenTests :: IO ()
runAddThenFlattenTests = do
  putStrLn "MPS addition commutes with flattening (vp = 2)..."
  QC.quickCheck prop_addThenFlattenVP2
  putStrLn "MPS addition commutes with flattening (vp = 3)..."
  QC.quickCheck prop_addThenFlattenVP3
  putStrLn "MPS physical basis vectors match Physical3 basis..."
  QC.quickCheck prop_basisMPSMatchesPhysicalVP2
  QC.quickCheck prop_basisMPSMatchesPhysicalVP3
  putStrLn "MPS decompose' matches Physical3 decompose'..."
  QC.quickCheck prop_decomposePrimeMatchesPhysicalVP2
  QC.quickCheck prop_decomposePrimeMatchesPhysicalVP3
  putStrLn "canonicalMPS round-trips on physical space..."
  QC.quickCheck prop_physicalRecomposeVP2
  QC.quickCheck prop_physicalRecomposeVP3
  putStrLn "mpsFromFlat round-trips on physical space..."
  QC.quickCheck prop_mpsFromFlatRoundTripVP2
  QC.quickCheck prop_mpsFromFlatRoundTripVP3


-- | Human-readable label for a 'Physical3' basis element.
showPhysicalBasis
  :: forall vp
   . (KnownNat vp, KnownNat (vp * vp), KnownNat (PhysicalDim3 vp))
  => Basis (Physical3 vp)
  -> String
showPhysicalBasis b =
  let (s1, s2, s3) = physicalIndicesFromBasis b
  in "|" ++ intercalate "," (map show [s1, s2, s3]) ++ "⟩"

-- | Sample a random @MPS 2@ and print one physical basis coefficient via
-- 'decompose''.
exampleDecomposeBasis :: IO ()
exampleDecomposeBasis = do
  let mps :: MPS 2 = sampleWithSeed 42 10 genMPS
      -- product state |0,1,1⟩ in left-associated @(C 2 ⊗ C 2) ⊗ C 2@
      b :: Basis (Physical3 2) = ((finites @2 !! 0, finites @2 !! 1), finites @2 !! 1)
  putStrLn ("Random MPS (seed 42, size 10); bond dim = " ++ show (bondDimMPS mps))
  putStrLn
    ( "decompose' at "
        ++ showPhysicalBasis @2 b
        ++ " = "
        ++ show (decompose' mps b)
    )
  putStrLn
    ( "Same coefficient from mpsToPhysical3: "
        ++ show (decompose' (mpsToPhysical3 mps) b)
    )
  putStrLn
    ( "Flat amplitude vector: "
        ++ show (extract (physicalToFlat (mpsToPhysical3 mps)))
    )

-- | A concrete non-zero @MPS 2@ with bond dimension 1, flattened to @C 8@.
test :: IO ()
test = do 
  print $ mpsToFlat nonZeroMPS
  print $ mpsToFlat (nonZeroMPS ^+^ nonZeroMPS)
  print $ mpsToFlat nonZeroMPS ^+^ mpsToFlat nonZeroMPS
  where
    nonZeroMPS :: MPS 2
    nonZeroMPS = MPS leftMap centerMap rightMap

    -- C 2 +> Bond: both physical basis vectors map to the length-1 bond [1].
    leftMap = LinearMap (V.fromList [unit, unit])

    -- Bond +> (C 2 ⊗ Bond): one bond-basis input, two physical rows.
    centerMap = LinearMap [Tensor (V.fromList [unit, unit])]

    -- Bond +> C 2: one bond-basis input mapping to a C 2 vector.
    rightMap = LinearMap [cvec [1, 2]]

    unit = FinSuppSeq (U.fromList [1])
    cvec xs = fromMaybe (error "test: create failed") (create (LA.fromList xs))

-- | Draw a single value from a 'QC.Gen' deterministically with a fixed seed.
--
-- @unGen :: Gen a -> QCGen -> Int -> a@ — the 'Int' is the QuickCheck size,
-- which controls how large generated structures are.
sampleWithSeed :: Int -> Int -> QC.Gen a -> a
sampleWithSeed seed genSize gen = unGen gen (mkQCGen seed) genSize

-- | Same as 'test', but on a random @MPS 2@ drawn from 'genMPS'
-- with a fixed seed (so it is reproducible). Note: depending on the seed the
-- draw can be the zero MPS, since 'genMPS' may pick bond dimension 0.
testRandom :: IO ()
testRandom = do
  print $ mpsToFlat randomMPS
  print $ mpsToFlat (randomMPS ^+^ randomMPS)
  print $ mpsToFlat randomMPS ^+^ mpsToFlat randomMPS
  where
    randomMPS :: MPS 2
    randomMPS = sampleWithSeed 42 10 genMPS