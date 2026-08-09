{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE ExplicitNamespaces #-}

-- | MPS bond-gauge bundle: Haar unitaries on virtual bonds and the natural
-- regauging action that leaves the physical state invariant.
--
-- For an open MPS with bulk length @n@ (total physical sites @n + 2@), there
-- are @n + 1@ internal bonds. A tuple @(u₀,…,uₙ) ∈ U(χ)^{n+1}@ acts by
--
--   left'      = u₀ ∘ left
--   bulk'_j    = u_{j+1} ∘ bulk_j ∘ (u_j† ⊗ id)
--   right'     = right ∘ uₙ†
--
-- which telescopes to the identity on the physical tensor.
module TensorNetwork.Bundle
  ( regaugeMPS
  , genBondGauges
  , prop_regaugePreservesPhysical
  ) where

import Prelude hiding (id, (.))
import Data.Maybe (fromMaybe)
import qualified Data.Vector as Vector
import GHC.TypeLits (KnownNat, type (+), natVal)
import Data.Proxy (Proxy (..))
import Linear.V (V (..))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import Math.LinearMap.Category (type (+>), type (⊗))
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C)
import qualified Test.QuickCheck as QC
import TensorNetwork.Categorical ((⊗^))
import TensorNetwork.LieGroup (genHaarUnitaryProduct)
import TensorNetwork.MPS.General
  ( MPS (..), dagger, hermitianNorm, MPSConstraints )
import TensorNetwork.MPS.Fixed
  ( genGaugeMPSC, physicalClose3 )

-- | Haar gauges on the @n + 1@ internal bonds of an @MPS _ _ n@.
genBondGauges
  :: forall χ n. (KnownNat χ, KnownNat n, KnownNat (n + 1))
  => QC.Gen (V (n + 1) (C χ +> C χ))
genBondGauges = genHaarUnitaryProduct @χ @(n + 1)

-- | Apply bond gauges in transfer orientation (see module header).
regaugeMPS
  :: forall χ p n.
  ( KnownNat χ
  , KnownNat p
  , KnownNat n
  , KnownNat (n + 1)
  , MPSConstraints (C χ) (C p)
  ) =>
  V (n + 1) (C χ +> C χ) -> MPS (C χ) (C p) n -> MPS (C χ) (C p) n
regaugeMPS (V us) (MPS l bulk r) =
  let nBulk = fromIntegral (natVal (Proxy @n)) :: Int
      uAt i =
        fromMaybe (error ("regaugeMPS: gauge index " ++ show i)) (us Vector.!? i)
      uDag i = dagger hermitianNorm hermitianNorm (uAt i)
      l' = uAt 0 . l
      bulk' =
        V $
          Vector.imap
            (\j b -> uAt (j + 1) . b . (uDag j ⊗^ (Cat.id :: C p +> C p)))
            (case bulk of V v -> v)
      r' = r . uDag nBulk
  in MPS l' bulk' r'

-- | Random bond gauges leave the flattened physical tensor unchanged (@n = 1@).
prop_regaugePreservesPhysical :: QC.Property
prop_regaugePreservesPhysical =
  QC.forAllBlind (genGaugeMPSC @3 @2 @1) $ \psi ->
    QC.forAllBlind (genBondGauges @3 @1) $ \us ->
      physicalClose3 1e-8 psi (regaugeMPS @3 @2 @1 us psi)
