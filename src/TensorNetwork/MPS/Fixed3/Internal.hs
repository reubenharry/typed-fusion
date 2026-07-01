{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE ConstraintKinds #-}

-- | Core types for typed-bond open-boundary MPS/MPO chains.
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
  , MPS3
  , MPO3
  , mps3
  , mpo3
  , withMPS3
  , withMPO3
  , ChainLength
  , Vector
  , cdim
  , basis
  , one1
  , OpWireNats
  ) where

import Math.LinearMap.Category (type (+>), type (⊗))
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, Sized (fromList))
import GHC.TypeLits (KnownNat, Nat, type (+), type (*), natVal)
import GHC.Exts (Constraint)
import Data.Proxy (Proxy (..))
import Data.Maybe (fromMaybe)
import Data.Vector.Sized (Vector, toList)
import qualified Data.Vector.Sized as VS

-- | 'KnownNat' bundle for 'opWire' and its callers (@⊗^@ on static bonds).
type OpWireNats p wl wr bl br =
  ( KnownNat p, KnownNat wl, KnownNat wr, KnownNat bl, KnownNat br
  , KnownNat (p * bl), KnownNat (bl * p), KnownNat (p * br), KnownNat (br * p)
  , p * bl ~ bl * p, p * br ~ br * p
  , KnownNat (wr * p), KnownNat (wl * p)
  , KnownNat (wr * br), KnownNat (wr * bl), KnownNat (wl * br), KnownNat (wl * bl)
  , KnownNat (wr * bl * p), KnownNat (wl * bl * p)
  , KnownNat (wl * br * p), KnownNat (wr * br * p)
  , KnownNat ((wr * bl) * p), KnownNat ((wl * bl) * p)
  , KnownNat ((wl * br) * p), KnownNat ((wr * br) * p)
  , KnownNat (wl * (bl * p)), KnownNat (wr * (bl * p))
  , KnownNat (wl * (br * p)), KnownNat (wr * (br * p))
  , KnownNat (wl * (p * bl)), KnownNat (wr * (p * bl))
  , KnownNat (wl * (p * br)), KnownNat (wr * (p * br)) )

-- | MPS site in transfer orientation: @incoming-bond ⊗ physical ↦
-- outgoing-bond@.
data Site (bl :: Nat) (p :: Nat) (br :: Nat) = Site
  { siteLin :: (C bl ⊗ C p) +> C br }

-- | Open-boundary MPS with @l@ bulk sites (@Site b p b@) between the typed
-- end sites. Chain length is @n = l + 2@; we require @l ≥ 1@ (so @n ≥ 3@).
data MPS (p :: Nat) (b :: Nat) (l :: Nat) = MPS
  { siteL :: Site 1 p b
  , sitesC :: Vector l (Site b p b)
  , siteR :: Site b p 1
  }

-- | Matching layout for the MPO on the same chain.
data MPO (p :: Nat) (w :: Nat) (l :: Nat) = MPO
  { opL :: OpSite 1 p w
  , opsC :: Vector l (OpSite w p w)
  , opR :: OpSite w p 1
  }

-- | Three-site chains (@l = 1@ bulk site, @n = 3@ total).
type MPS3 p b = MPS p b 1
type MPO3 p w = MPO p w 1

-- | Build a three-site MPS from its left, centre, and right sites.
mps3
  :: Site 1 p b -> Site b p b -> Site b p 1 -> MPS3 p b
mps3 s1 s2 s3 =
  MPS s1 (fromMaybe (error "mps3: bulk vector") (VS.fromList [s2])) s3

-- | Build a three-site MPO from its left, centre, and right operator sites.
mpo3
  :: OpSite 1 p w -> OpSite w p w -> OpSite w p 1 -> MPO3 p w
mpo3 o1 o2 o3 =
  MPO o1 (fromMaybe (error "mpo3: bulk vector") (VS.fromList [o2])) o3

-- | Destruct a three-site MPS.
withMPS3
  :: MPS3 p b
  -> (Site 1 p b -> Site b p b -> Site b p 1 -> a)
  -> a
withMPS3 (MPS s1 bulk s3) k = k s1 (bulkAt0 bulk) s3
  where
    bulkAt0 v = toList v !! 0

-- | Destruct a three-site MPO.
withMPO3
  :: MPO3 p w
  -> (OpSite 1 p w -> OpSite w p w -> OpSite w p 1 -> a)
  -> a
withMPO3 (MPO o1 bulk o3) k = k o1 (bulkAt0 bulk) o3
  where
    bulkAt0 v = toList v !! 0

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

-- | Dimension of @C n@ at the value level.
cdim :: forall n. KnownNat n => Int
cdim = fromIntegral (natVal (Proxy @n))

-- | Standard basis vector @|i⟩@ of @C n@ (data entry, not computation).
basis :: forall n. KnownNat n => Int -> C n
basis i = fromList [ if j == i then 1 else 0 | j <- [0 .. cdim @n - 1] ]

-- | The canonical boundary-bond vector @1 ∈ C 1@.
one1 :: C 1
one1 = basis @1 0
