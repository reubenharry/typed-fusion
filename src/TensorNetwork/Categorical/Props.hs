{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

-- | QuickCheck properties for 'TensorNetwork.Categorical' and
-- 'TensorNetwork.Dagger', pinned against explicit coefficient oracles.
-- Entries are small Gaussian integers so all comparisons are exact ('===').
--
-- These properties are also the regression suite for the backend behaviour of
-- 'vectorConjugate' on tensor/map spaces over @C n@ (ROADMAP §4a step 5).
module TensorNetwork.Categorical.Props where

import Prelude hiding (($), (.), id)
import Control.Category.Constrained (id, (.))
import Control.Arrow.Constrained (arr)
import Control.Arrow.Constrained (($))
import Math.LinearMap.Category
  ( type (+>), type (⊗), (⊗)
  , FiniteDimensional (..), SubBasis, decomposeLinMap
  , getLinearMap, LinearMap (..), applyLinear, getLinearFunction, (-+$>) )
import Math.VectorSpace.DimensionAware
  ( toArray, unsafeFromArray, dimensionality, DimensionalityCases(..)
  , unsafeFromArrayWithOffset, StaticDimensional )
import qualified Numeric.LinearAlgebra.HMatrix as HM
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, Sized (fromList, unwrap, create, konst), extract, M)
import Numeric.LinearAlgebra.Static.MPSLayout (siteLinearMap)
import Data.Maybe (fromJust)
import GHC.TypeLits (KnownNat, type (*), natVal)
import Data.Proxy (Proxy (..))
import Data.Complex (Complex ((:+)), conjugate)
import Data.VectorSpace (VectorSpace ((*^)), sumV)
import Control.Monad (replicateM)
import qualified Data.Vector.Storable as VS
import qualified Test.QuickCheck as QC

import TensorNetwork.Categorical
  ( (⊗^), swapMap, lassocMap, rassocMap
  , conjugateMap )

import TensorNetwork.MPS.LinmapStorage 


cdim :: forall n. KnownNat n => Int
cdim = fromIntegral (natVal (Proxy @n))
--------------------------------------------------------------------------------
-- Generators (small Gaussian integers, exact arithmetic)
--------------------------------------------------------------------------------

smallComplex :: QC.Gen (Complex Double)
smallComplex = do
  r <- QC.elements [-2 .. 2 :: Int]
  i <- QC.elements [-2 .. 2 :: Int]
  pure (fromIntegral r :+ fromIntegral i)

genC :: forall n. KnownNat n => QC.Gen (C n)
genC = fromList <$> replicateM (cdim @n) smallComplex

-- | Random @C n +> C m@ in the canonical basis.
genMap :: forall n m. (KnownNat n, KnownNat m) => QC.Gen (C n +> C m)
genMap = do
  imgs <- replicateM (cdim @n) (genC @m)
  pure (fst (recomposeLinMap (entireBasis :: SubBasis (C n)) imgs))

-- | Random site-shaped map @(C bl ⊗ C p) +> C br@ (column storage).
genSiteMap
  :: forall bl p br
   . (KnownNat bl, KnownNat p, KnownNat br, KnownNat (bl * p), KnownNat (p * br))
  => QC.Gen ((C bl ⊗ C p) +> C br)
genSiteMap =
  undefined <$> replicateM (cdim @bl * cdim @p) (genC @br)

--------------------------------------------------------------------------------
-- Monoidal product, braiding, associators, unitors
--------------------------------------------------------------------------------

-- | Show-free exact equality (the tensor/map spaces have 'Eq' but no 'Show').
(=~=) :: Eq a => a -> a -> QC.Property
x =~= y = QC.property (x == y)
infix 4 =~=

