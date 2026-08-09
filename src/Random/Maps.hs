{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Compositional sampling of linear maps: scalars → vectors → matrices →
-- Schur blocks → intertwiner spines.
--
-- An intertwiner is drawn as an independent product of coefficient matrices
-- along @IntertwinerHom g r q@ (Schur form); forgetful expansion stays elsewhere.
module Random.Maps
  ( -- * Scalars
    genGaussian
  , genComplexGaussian
    -- * Vectors / dense maps
  , genC
  , genMat
  , genLinMapC
  , genEndo
  , genBulkSiteC2
    -- * Schur blocks / intertwiners
  , genU1HomBlock
  , GenHomSectors (..)
  , genIntertwiner
  ) where

import Control.Monad (replicateM)
import Data.Complex (Complex (..))
import Data.Proxy (Proxy (..))
import qualified Data.Vector as Vector
import GHC.TypeLits (KnownNat, Nat, natVal, type (*))
import Linear.V (V (..))
import Math.LinearMap.Category (type (+>), type (⊗), LinearMap (..))
import Numeric.LinearAlgebra.Static (C, M, Sized (fromList), konst)
import qualified Test.QuickCheck as QC
import Symmetry.FunctorExperiment
  ( IntertwinerG (..), IntertwinerSectorsG (..) )
import Symmetry.Group (Group (..), Irreps, IntertwinerHom)
import Symmetry.HomBlock (HomBlockDim, U1HomBlock (..))
import TensorNetwork.MPS.LinmapStorage (linMapFromColumnImages)

--------------------------------------------------------------------------------
-- Scalars
--------------------------------------------------------------------------------

-- | Standard normal via Box–Muller (QuickCheck 'Gen').
genGaussian :: QC.Gen Double
genGaussian = do
  u1 <- QC.choose (1e-12, 1 - 1e-12)
  u2 <- QC.choose (0, 1)
  let r = sqrt (-2 * log u1)
      theta = 2 * pi * u2
  pure (r * cos theta)

-- | Complex normal with i.i.d. @N(0,1)@ real\/imag parts.
genComplexGaussian :: QC.Gen (Complex Double)
genComplexGaussian = (:+) <$> genGaussian <*> genGaussian

--------------------------------------------------------------------------------
-- Vectors / dense maps
--------------------------------------------------------------------------------

genC :: forall n. KnownNat n => QC.Gen (C n)
genC = do
  let n = fromIntegral (natVal (Proxy @n))
  xs <- replicateM n genComplexGaussian
  pure (fromList xs)

genMat :: forall m n. (KnownNat m, KnownNat n, KnownNat (m * n)) => QC.Gen (M m n)
genMat = do
  let entries = fromIntegral (natVal (Proxy @(m * n)))
  xs <- replicateM entries genComplexGaussian
  pure (fromList xs)

-- | @C dom +> C cod@ from independent Gaussian column images.
genLinMapC :: forall dom cod. (KnownNat dom, KnownNat cod) => QC.Gen (C dom +> C cod)
genLinMapC =
  linMapFromColumnImages @dom @cod
    <$> replicateM (fromIntegral (natVal (Proxy @dom))) (genC @cod)

-- | Alias kept for existing MPS call sites (@domain@ first, matching historical 'genEndo').
genEndo :: forall n m. (KnownNat n, KnownNat m) => QC.Gen (C n +> C m)
genEndo = genLinMapC @n @m

-- | Placeholder bulk (all-ones). Prefer a left-SVD flatten generator at the
-- call site when a truly random bulk is needed.
genBulkSiteC2
  :: forall n m (q :: Nat)
   . (KnownNat n, KnownNat m, KnownNat q, KnownNat (m * n), KnownNat (n * m))
  => QC.Gen (V q ((C n ⊗ C m) +> C n))
genBulkSiteC2 =
  pure $ V $ Vector.replicate (fromIntegral (natVal (Proxy @q))) (LinearMap (konst 1))

--------------------------------------------------------------------------------
-- Schur blocks / intertwiners
--------------------------------------------------------------------------------

genU1HomBlock
  :: forall m n. (KnownNat m, KnownNat n, KnownNat (HomBlockDim m n))
  => QC.Gen (U1HomBlock m n)
genU1HomBlock = U1HomBlock <$> genMat @m @n

-- | Draw one independent coefficient block per hom-sector entry.
class GenHomSectors (g :: Group) (hom :: [(Irreps g, Nat, Nat)]) where
  genHomSectors :: QC.Gen (IntertwinerSectorsG g hom)

instance GenHomSectors U1 '[] where
  genHomSectors = pure InterNil

instance
  ( KnownNat m, KnownNat n, KnownNat (HomBlockDim m n)
  , GenHomSectors U1 rest
  ) => GenHomSectors U1 ('(z, m, n) ': rest) where
  genHomSectors = InterCons <$> genU1HomBlock @m @n <*> genHomSectors

instance GenHomSectors SU2 '[] where
  genHomSectors = pure InterNil

instance
  ( KnownNat m, KnownNat n, KnownNat (HomBlockDim m n)
  , GenHomSectors SU2 rest
  ) => GenHomSectors SU2 ('(j, m, n) ': rest) where
  genHomSectors = InterCons <$> genU1HomBlock @m @n <*> genHomSectors

genIntertwiner
  :: forall g r q
   . GenHomSectors g (IntertwinerHom g r q)
  => QC.Gen (IntertwinerG g r q)
genIntertwiner = MkIntertwiner <$> genHomSectors
