{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

-- | A finite, typed-bond, three-site matrix product state.
--
-- Design (see ROADMAP §4a — settled):
--
--   * __Site orientation: transfer / contraction.__ Each site is a linear map
--     taking @incoming-bond ⊗ physical@ to @outgoing-bond@. The boundary bonds
--     are the monoidal unit @C 1@. Bonds are typed (@KnownNat@), so a
--     bond-dimension mismatch between adjacent sites is a type error.
--
--   * Physical dimension @p@, bond dimensions @b1@ (between sites 1–2) and
--     @b2@ (between sites 2–3).
--
-- The amplitude of a configuration @(s₁, s₂, s₃)@ is
--
--   @ψ(s₁,s₂,s₃) = Σ_{l₁,l₂} L[(1,s₁),l₁] · C[(l₁,s₂),l₂] · R[(l₂,s₃),1]@
--
-- which 'mpsToFlat' evaluates by threading the bond vector through the three
-- site maps (no morphism-level tensor products or associators needed — just
-- vector tensoring '⊗' and map application '$').
module MPS
  ( MPS (..)
  , mpsToFlat
  ) where

import Prelude hiding (($))
import Control.Arrow.Constrained (($))
import Math.LinearMap.Category (type (+>), type (⊗), (⊗))
-- Orphan instances making @C n@ (and tensors over it) linearmap-category spaces.
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, create, extract)
import qualified Numeric.LinearAlgebra as H
import GHC.TypeLits (KnownNat, Nat, natVal, type (*))
import Data.Proxy (Proxy (..))
import Data.Maybe (fromMaybe)
import Data.Complex (Complex)

-- | A three-site MPS in transfer orientation. @p@ is the physical dimension;
-- @b1@, @b2@ are the two internal bond dimensions.
data MPS (p :: Nat) (b1 :: Nat) (b2 :: Nat) = MPS
  { siteL :: (C 1  ⊗ C p) +> C b1  -- ^ left:   (boundary ⊗ physical) → bond₁
  , siteC :: (C b1 ⊗ C p) +> C b2  -- ^ centre: (bond₁    ⊗ physical) → bond₂
  , siteR :: (C b2 ⊗ C p) +> C 1   -- ^ right:  (bond₂    ⊗ physical) → boundary
  }

-- | The dimension of @C n@ as a value.
cdim :: forall n. KnownNat n => Int
cdim = fromIntegral (natVal (Proxy @n))

-- | The @i@-th standard basis vector of @C n@.
basis :: forall n. KnownNat n => Int -> C n
basis i =
  fromMaybe (error "MPS.basis: create failed") $
    create (H.fromList [ if j == i then 1 else 0 | j <- [0 .. cdim @n - 1] ])

-- | The unit vector of @C 1@.
one1 :: C 1
one1 = basis @1 0

-- | Contract the MPS into its physical state vector @C (p³)@ ("map to physical
-- space"). The flat index ordering is @(s₁,s₂,s₃) ↦ (s₁·p + s₂)·p + s₃@ — the
-- same convention as @Infinite.mpsToFlat@, so the two are directly comparable.
--
-- This is the oracle generator for later operations (inner products,
-- expectation values): its @C n@ inner product conjugates correctly.
mpsToFlat
  :: forall p b1 b2.
     (KnownNat p, KnownNat b1, KnownNat b2, KnownNat (p * p * p))
  => MPS p b1 b2 -> C (p * p * p)
mpsToFlat (MPS sL sC sR) =
  fromMaybe (error "MPS.mpsToFlat: create failed") $
    create (H.fromList amplitudes)
  where
    p = cdim @p
    amplitudes :: [Complex Double]
    amplitudes =
      [ amplitude s1 s2 s3
      | s1 <- [0 .. p - 1], s2 <- [0 .. p - 1], s3 <- [0 .. p - 1] ]

    amplitude :: Int -> Int -> Int -> Complex Double
    amplitude s1 s2 s3 =
      let v1 = sL $ (one1        ⊗ basis @p s1)  -- :: C b1
          v2 = sC $ (v1          ⊗ basis @p s2)  -- :: C b2
          r  = sR $ (v2          ⊗ basis @p s3)  -- :: C 1
      in H.atIndex (extract r) 0
