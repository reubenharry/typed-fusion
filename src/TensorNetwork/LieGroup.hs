{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}

-- | Sampling from classical compact Lie groups (Haar measure).
--
-- 'genHaarUnitary' draws from @U(n)@ via the Ginibre + QR construction of
-- Mezzadri (2007): complex Gaussians → QR → diagonal phase fix on @R@.
-- 'genHaarUnitaryProduct' draws an independent product @U(n)ᵏ@.
module TensorNetwork.LieGroup
  ( genHaarUnitary
  , genHaarUnitaryProduct
  , prop_haarUnitary
  ) where

-- Gaussian scalar sampling lives in 'Random.Maps'; Haar builds on it.

import Prelude hiding (id, (.))
import Control.Monad (replicateM)
import Data.Complex (Complex (..), magnitude)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import GHC.TypeLits (KnownNat, natVal)
import qualified Data.Vector as Vector
import Linear.V (V (..))
import Control.Category.Constrained (id, (.))
import Control.Arrow.Constrained (arr)
import Math.LinearMap.Category
  ( type (+>), type (-+>), LinearMap (..) )
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, M, Sized (create, extract))
import qualified Numeric.LinearAlgebra as HM
import qualified Test.QuickCheck as QC
import Random.Maps (genComplexGaussian)
import TensorNetwork.MPS.General (dagger, hermitianNorm)

-- | Unit phase of a complex scalar (@0 ↦ 1@).
unitPhase :: Complex Double -> Complex Double
unitPhase z =
  let m = magnitude z
  in if m == 0 then 1 else z / (m :+ 0)

-- | Haar-random element of @U(n)@ as @C n +> C n@.
genHaarUnitary :: forall n. KnownNat n => QC.Gen (C n +> C n)
genHaarUnitary = do
  let n = fromIntegral (natVal (Proxy @n))
  entries <- replicateM (n * n) genComplexGaussian
  let a = (n HM.>< n) entries :: HM.Matrix (Complex Double)
      (q0, r) = HM.thinQR a
      phases = HM.cmap unitPhase (HM.takeDiag r)
      q = q0 HM.<> HM.diag phases
      m = fromMaybe (error "genHaarUnitary: static size mismatch") (create q) :: M n n
  pure (LinearMap m)

-- | Independent product of @k@ Haar draws from @U(n)@.
genHaarUnitaryProduct
  :: forall n k. (KnownNat n, KnownNat k) => QC.Gen (V k (C n +> C n))
genHaarUnitaryProduct = do
  let k = fromIntegral (natVal (Proxy @k))
  us <- replicateM k (genHaarUnitary @n)
  pure (V (Vector.fromList us))

maxDiffM :: KnownNat n => C n +> C n -> C n +> C n -> Double
maxDiffM (LinearMap a) (LinearMap b) =
  let da = extract a
      db = extract b
  in HM.maxElement (HM.cmap magnitude (da - db))

-- | Sampled @U@ satisfies @U† U ≈ I@ and @U U† ≈ I@.
prop_haarUnitary :: QC.Property
prop_haarUnitary =
  QC.forAllBlind (genHaarUnitary @3) $ \u ->
    let uDag = dagger hermitianNorm hermitianNorm u
        id3 = arr (id :: C 3 -+> C 3) :: C 3 +> C 3
        left = uDag . u
        right = u . uDag
    in  maxDiffM left id3 < 1e-10
     QC..&&. maxDiffM right id3 < 1e-10
