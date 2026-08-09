{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | QuickCheck orphans for static vectors, plus re-exports of map generators
-- from 'Random.Maps' for existing call sites.
module Random.Arbitrary
  ( module Random.Maps
  , randomGaussian
  , randomGaussianIO
  , randomComplex
  ) where

import qualified Test.QuickCheck as QC
import GHC.TypeLits (KnownNat, natVal)
import Numeric.LinearAlgebra.Static (R, C, Sized (..), toComplex)
import Data.Maybe (fromMaybe)
import Data.Data (Proxy (..))
import System.Random.Stateful
import qualified Data.Vector.Storable as V
import Math.TensorNetwork (Field)
import Random.Maps

-- | Draw a real number from a standard normal N(0,1) using the Box-Muller transform.
randomGaussian :: RandomGen g => g -> (Double, g)
randomGaussian g =
  let (u1, g') = random g
      (u2, g'') = random g'
      u1' = if u1 == 0 then 1e-10 else u1  -- avoid log 0
      r = sqrt (- (2 * log u1'))
      theta = 2 * pi * u2
  in (r * cos theta, g'')

-- | Draw a real number from N(0,1) using the global random generator.
randomGaussianIO :: IO Double
randomGaussianIO = getStdRandom randomGaussian

randomComplex :: QC.Gen Field
randomComplex = QC.arbitrary

instance KnownNat p => QC.Arbitrary (R p) where
  arbitrary :: KnownNat p => QC.Gen (R p)
  arbitrary = do
    let n = natVal (Proxy @p)
    r1 <- V.replicateM (fromIntegral n) QC.arbitrary
    return $ fromMaybe undefined $ create r1

instance KnownNat p => QC.Arbitrary (C p) where
  arbitrary = do
    r1 <- QC.arbitrary
    r2 <- QC.arbitrary
    return (toComplex (r1, r2))
