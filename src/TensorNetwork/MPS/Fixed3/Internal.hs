{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE GADTs #-}

-- | Core types for the typed-bond 3-site MPS\/MPO.
--
-- Only types and standard-basis data-entry helpers live here. All
-- coefficient-level computation is in "TensorNetwork.MPS.Fixed3.Reference"
-- (QuickCheck oracles only); the production contraction path in
-- "TensorNetwork.MPS.Fixed3" is morphism-level.
module TensorNetwork.MPS.Fixed3.Internal
  ( Site (..)
  , MPS (..)
  , OpSite (..)
  , MPO (..)
  , MPSGeneral (..)
  , MPOGeneral (..)
  , ChainLength
  , Vector
  , cdim
  , basis
  , one1
  ) where

import Math.LinearMap.Category (type (+>), type (⊗))
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, Sized (fromList))
import GHC.TypeLits (KnownNat, Nat, type (+), natVal)
import Data.Proxy (Proxy (..))
import Data.Vector.Sized (Vector)

-- | MPS site in transfer orientation: @incoming-bond ⊗ physical ↦
-- outgoing-bond@.
data Site (bl :: Nat) (p :: Nat) (br :: Nat) = Site
  { siteLin :: (C bl ⊗ C p) +> C br }

data MPS (p :: Nat) (b :: Nat)  = MPS
  { siteL :: Site 1  p b
  , siteC :: Site b p b
  , siteR :: Site b p 1
  }

-- | Open-boundary MPS with @l@ bulk sites (@Site b p b@) between the typed
-- end sites. Chain length is @n = l + 2@; we require @l ≥ 1@ (so @n ≥ 3@).
data MPSGeneral (p :: Nat) (b :: Nat) (l :: Nat) = MPSGeneral
  { siteLGeneral :: Site 1 p b
  , sitesC :: Vector l (Site b p b)
  , siteRGeneral :: Site b p 1
  }

-- | Matching layout for the MPO on the same chain.
data MPOGeneral (p :: Nat) (w :: Nat) (l :: Nat) = MPOGeneral
  { opLGeneral :: OpSite 1 p w
  , opsC :: Vector l (OpSite w p w)
  , opRGeneral :: OpSite w p 1
  }

-- | Total site count for @l@ bulk sites.
type ChainLength l = l + 2

-- | MPO site in transfer orientation: the domain physical leg is the
-- operator /output/ (bra-side) index @t@, the codomain physical leg the
-- /input/ (ket-side) index @s@. With this orientation a left-to-right
-- ⟨ψ|H|φ⟩ contraction is a chain of forward compositions: @dagger bra@
-- emits @t@, the MPO site consumes it and emits @s@, the ket site consumes
-- @s@ — no partial transposes anywhere in the production path.
--
-- Data entry: to put an operator block @O@ (with matrix elements
-- @O_{ts} = ⟨t|O|s⟩@) on a site, store the map @e_t ↦ Σ_s O_{ts} e_s@,
-- i.e. the /transpose/ of @O@ ('TensorNetwork.Dagger.transposeMap').
data OpSite (wl :: Nat) (p :: Nat) (wr :: Nat) = OpSite
  { opSiteLin :: (C wl ⊗ C p) +> (C wr ⊗ C p) }

data MPO (p :: Nat) (w :: Nat) = MPO
  { opL :: OpSite 1  p w
  , opC :: OpSite w p w
  , opR :: OpSite w p 1
  }

-- | Dimension of @C n@ at the value level.
cdim :: forall n. KnownNat n => Int
cdim = fromIntegral (natVal (Proxy @n))

-- | Standard basis vector @|i⟩@ of @C n@ (data entry, not computation).
basis :: forall n. KnownNat n => Int -> C n
basis i = fromList [ if j == i then 1 else 0 | j <- [0 .. cdim @n - 1] ]

-- | The canonical boundary-bond vector @1 ∈ C 1@.
one1 :: C 1
one1 = basis @1 0
