{-# LANGUAGE TypeApplications #-}

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
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Random where

import qualified Test.QuickCheck as QC
import Data.Complex (Complex)
import TensorNetwork
import System.Random (RandomGen)
import GHC.TypeLits (KnownNat, natVal)
import Numeric.LinearAlgebra.Static (R, C, Sized (..), toComplex)
import Data.Maybe (fromMaybe)
import Data.Vector.Generic (replicateM)
import Data.Data (Proxy(..))
import System.Random.Stateful

-- | Draw a real number from a standard normal N(0,1) using the Box-Muller transform.
randomGaussian :: RandomGen g => g -> (Double, g)
randomGaussian g =
  let (u1, g') = random g
      (u2, g'') = random g'
      u1' = if u1 == 0 then 1e-10 else u1  -- avoid log 0
      r = sqrt (-2 * log u1')
      theta = 2 * pi * u2
  in (r * cos theta, g'')

-- | Draw a real number from N(0,1) using the global random generator.
randomGaussianIO :: IO Double
randomGaussianIO = getStdRandom randomGaussian

randomComplex :: QC.Gen Field
randomComplex = QC.arbitrary



-- instance QC.Arbitrary (VB Field) where
--     arbitrary = do
--         V3 <$> QC.arbitrary <*> QC.arbitrary <*> QC.arbitrary

-- instance QC.Arbitrary (VB Double) where
--     arbitrary = do
--         V3 <$> QC.arbitrary <*> QC.arbitrary <*> QC.arbitrary



-- randomMatrixIO :: IO (Ham VP)
-- randomMatrixIO = QC.generate randomMatrix

-- instance QC.Arbitrary field => QC.Arbitrary (V2 field) where
--     arbitrary = V2 <$> QC.arbitrary <*> QC.arbitrary

-- randomMatrix :: QC.Gen (Ham VP)
-- randomMatrix = QC.arbitrary



-- instance Semimanifold (Complex Double) where
--     -- semimanifoldWitness = SemimanifoldWitness BoundarylessWitness

-- instance PseudoAffine (Complex Double) where

-- instance AffineSpace (Complex Double) where
--     type Diff (Complex Double) = Complex Double
--     (.+^) = (^+^)
--     (.-.) = (^-^)

-- instance TensorSpace (Complex Double) where


instance KnownNat p => QC.Arbitrary (R p) where
    arbitrary :: KnownNat p => QC.Gen (R p)
    arbitrary = do
        let n = natVal (Proxy @p)
        r1 <- replicateM (fromIntegral n) QC.arbitrary
        return $ fromMaybe undefined $ create r1


instance KnownNat p => QC.Arbitrary (C p) where
    arbitrary = do
        r1 <- QC.arbitrary
        r2 <- QC.arbitrary
        return (toComplex (r1, r2))

instance (KnownNat p, KnownNat b) => QC.Arbitrary (MPS p b) where
    arbitrary :: (KnownNat p, KnownNat b) => QC.Gen (MPS p b)
    arbitrary =  do
        leftMPS <- QC.arbitrary
        centerMPS <- QC.arbitrary
        MPS leftMPS centerMPS <$> QC.arbitrary