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
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Random.Arbitrary where

import qualified Test.QuickCheck as QC
import Data.Complex (Complex)
import System.Random (RandomGen)
import GHC.TypeLits (KnownNat, natVal, Nat, type (*))
import Numeric.LinearAlgebra.Static (R, C, Sized (..), toComplex)
import Data.Maybe (fromMaybe)
import Data.Vector.Generic ()
import Data.Data (Proxy(..))
import System.Random.Stateful
import Math.LinearMap.Category (type (+>), LinearMap (..), type (⊗))
import TensorNetwork.MPS.LinmapStorage
import Linear.V (V (..))
import Prelude hiding (id, ($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($), arr)
import qualified Data.Vector as Vector
import Control.Monad (replicateM)
import qualified Data.Vector.Storable as V
import Math.TensorNetwork (Field)



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

genEndo :: forall n m . (KnownNat n, KnownNat m) => QC.Gen (C n +> C m)
genEndo = linMapFromColumnImages @n @m <$> replicateM (fromIntegral (natVal (Proxy @n))) (QC.arbitrary @(C m))

-- | Placeholder bulk (all-ones). Prefer a left-SVD flatten generator at the
-- call site when a truly random bulk is needed (tensor-domain 'LinearMap'
-- layout is not the same as flat @C (n·m)@ column packing).
genBulkSiteC2
  :: forall n m (q :: Nat)
   . (KnownNat n, KnownNat m, KnownNat q, KnownNat (m * n), KnownNat (n * m))
  => QC.Gen (V q ((C n ⊗ C m) +> C n))
genBulkSiteC2 =
  pure $ V $ Vector.replicate (fromIntegral (natVal (Proxy @q))) (LinearMap (konst 1))

genLinMapC :: forall dom cod . (KnownNat dom, KnownNat cod) => QC.Gen (C dom +> C cod)
genLinMapC =
  linMapFromColumnImages @dom @cod
    <$> replicateM (fromIntegral (natVal (Proxy @dom))) (QC.arbitrary @(C cod))

-- instance QC.Arbitrary (LinearMap (Complex Double)(C n) (C m))where 

-- instance (KnownNat p, KnownNat b) => QC.Arbitrary (MPS p b) where
--     arbitrary :: (KnownNat p, KnownNat b) => QC.Gen (MPS p b)
--     arbitrary =  do
--         leftMPS <- QC.arbitrary
--         centerMPS <- QC.arbitrary
--         MPS leftMPS centerMPS <$> QC.arbitrary

