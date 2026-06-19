{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

-- | General-length MPS/MPO storage, indexing, and 3-site record bridges.
module TensorNetwork.DMRG.Chain
  ( -- * Chain length
    chainLength
    -- * Site / operator roles
  , SomeSite (..)
  , SomeOpSite (..)
    -- * Indexing
  , getSite
  , setSite
  , getOp
  , setOp
    -- * 3-site record bridge
  , mps3ToGeneral
  , mps3FromGeneral
  , mpo3ToGeneral
  , mpo3FromGeneral
    -- * Zipper reassembly (3-site, until zipper uses 'MPSGeneral' directly)
  , AssembleMPS3FromZipper (..)
  , assembleMPS3FromZipper
    -- * Indexed updates on the 3-site record
  , PatchMPSAt (..)
  , patchMPSAt
  , MPOAt (..)
  , mpoSiteAt
  ) where

import GHC.TypeLits (Nat, KnownNat, natVal)
import Data.Proxy (Proxy (..))
import Data.Maybe (fromMaybe)
import Data.List (splitAt)
import Data.Vector.Sized (Vector, fromList, toList)
import TensorNetwork.DMRG.Spine (HList (..))
import qualified TensorNetwork.DMRG.Spine as Spine
import TensorNetwork.DMRG.SiteLists (LeftSites, RightSites, SiteAt, OpSiteAt)
import TensorNetwork.MPS.Fixed3.Internal
  ( Site (..), MPS (..), OpSite (..), MPO (..)
  , MPSGeneral (..), MPOGeneral (..), ChainLength )

bulkAt :: Int -> Vector l a -> a
bulkAt j v = toList v !! j

bulkUpdate :: forall l a. KnownNat l => Int -> a -> Vector l a -> Vector l a
bulkUpdate j x v =
  fromMaybe (error "bulkUpdate: length mismatch") (fromList (pre ++ x : post))
  where
    (pre, _:post) = splitAt j (toList v)

-- | Value-level chain length (@l + 2@ bulk + boundary sites).
chainLength :: forall l. KnownNat l => Int
chainLength = fromIntegral (natVal (Proxy @l)) + 2

-- | A site drawn from an 'MPSGeneral', tagged by its bond layout.
data SomeSite p b where
  SiteLeft  :: Site 1 p b -> SomeSite p b
  SiteBulk  :: Site b p b -> SomeSite p b
  SiteRight :: Site b p 1 -> SomeSite p b

data SomeOpSite p w where
  OpLeft  :: OpSite 1 p w -> SomeOpSite p w
  OpBulk  :: OpSite w p w -> SomeOpSite p w
  OpRight :: OpSite w p 1 -> SomeOpSite p w

-- | Read site @i@ (1-based, @1 ≤ i ≤ chainLength@).
getSite
  :: forall p b l
   . KnownNat l
  => Int
  -> MPSGeneral p b l
  -> SomeSite p b
getSite i mps
  | i == 1 = SiteLeft (siteLGeneral mps)
  | i == chainLength @l = SiteRight (siteRGeneral mps)
  | i >= 2 && i <= chainLength @l - 1 = SiteBulk (bulkAt (i - 2) (sitesC mps))
  | otherwise =
      error ("getSite: index " ++ show i ++ " out of range 1.." ++ show (chainLength @l))

-- | Write site @i@ (1-based). The 'SomeSite' constructor must match @i@.
setSite
  :: forall p b l
   . KnownNat l
  => Int
  -> SomeSite p b
  -> MPSGeneral p b l
  -> MPSGeneral p b l
setSite 1 (SiteLeft s) mps = mps { siteLGeneral = s }
setSite i (SiteBulk s) mps
  | i >= 2 && i <= chainLength @l - 1 =
      mps { sitesC = bulkUpdate (i - 2) s (sitesC mps) }
  | otherwise = siteIndexError @l "setSite" i
setSite i (SiteRight s) mps
  | i == chainLength @l = mps { siteRGeneral = s }
  | otherwise = siteIndexError @l "setSite" i
setSite i _ _ = siteIndexError @l "setSite" i

siteIndexError :: forall l a. KnownNat l => String -> Int -> a
siteIndexError what i =
  error (what ++ ": index " ++ show i ++ " out of range 1.." ++ show (chainLength @l))

getOp
  :: forall p w l
   . KnownNat l
  => Int
  -> MPOGeneral p w l
  -> SomeOpSite p w
getOp i mpo
  | i == 1 = OpLeft (opLGeneral mpo)
  | i == chainLength @l = OpRight (opRGeneral mpo)
  | i >= 2 && i <= chainLength @l - 1 = OpBulk (bulkAt (i - 2) (opsC mpo))
  | otherwise =
      error ("getOp: index " ++ show i ++ " out of range 1.." ++ show (chainLength @l))

setOp
  :: forall p w l
   . KnownNat l
  => Int
  -> SomeOpSite p w
  -> MPOGeneral p w l
  -> MPOGeneral p w l
setOp 1 (OpLeft o) mpo = mpo { opLGeneral = o }
setOp i (OpBulk o) mpo
  | i >= 2 && i <= chainLength @l - 1 =
      mpo { opsC = bulkUpdate (i - 2) o (opsC mpo) }
  | otherwise = siteIndexError @l "setOp" i
setOp i (OpRight o) mpo
  | i == chainLength @l = mpo { opRGeneral = o }
  | otherwise = siteIndexError @l "setOp" i
setOp i _ _ = siteIndexError @l "setOp" i

mps3ToGeneral :: MPS p b -> MPSGeneral p b 1
mps3ToGeneral (MPS s1 s2 s3) =
  MPSGeneral s1 (fromMaybe (error "mps3ToGeneral: bulk vector") (fromList [s2])) s3

mps3FromGeneral :: MPSGeneral p b 1 -> MPS p b
mps3FromGeneral (MPSGeneral s1 bulk s3) = MPS s1 (bulkAt 0 bulk) s3

mpo3ToGeneral :: MPO p w -> MPOGeneral p w 1
mpo3ToGeneral (MPO o1 o2 o3) =
  MPOGeneral o1 (fromMaybe (error "mpo3ToGeneral: bulk vector") (fromList [o2])) o3

mpo3FromGeneral :: MPOGeneral p w 1 -> MPO p w
mpo3FromGeneral (MPOGeneral o1 bulk o3) = MPO o1 (bulkAt 0 bulk) o3

class AssembleMPS3FromZipper (i :: Nat) where
  assembleMPS3FromZipper
    :: forall p b. KnownNat b
    => HList (LeftSites 3 p b i)
    -> SiteAt 3 p b i
    -> HList (RightSites 3 p b i)
    -> MPS p b

instance AssembleMPS3FromZipper 1 where
  assembleMPS3FromZipper
    :: forall p b. KnownNat b
    => HList (LeftSites 3 p b 1)
    -> SiteAt 3 p b 1
    -> HList (RightSites 3 p b 1)
    -> MPS p b
  assembleMPS3FromZipper HNil c rs =
    MPS c (Spine.spineHead rs) (Spine.spineHead (Spine.spineTail rs))

instance AssembleMPS3FromZipper 2 where
  assembleMPS3FromZipper
    :: forall p b. KnownNat b
    => HList (LeftSites 3 p b 2)
    -> SiteAt 3 p b 2
    -> HList (RightSites 3 p b 2)
    -> MPS p b
  assembleMPS3FromZipper (s1 :& HNil) c (s3 :& HNil) = MPS s1 c s3

instance AssembleMPS3FromZipper 3 where
  assembleMPS3FromZipper
    :: forall p b. KnownNat b
    => HList (LeftSites 3 p b 3)
    -> SiteAt 3 p b 3
    -> HList (RightSites 3 p b 3)
    -> MPS p b
  assembleMPS3FromZipper (s1 :& s2 :& HNil) c HNil = MPS s1 s2 c

class PatchMPSAt (i :: Nat) where
  patchMPSAtImpl
    :: forall p b. KnownNat b => SiteAt 3 p b i -> MPS p b -> MPS p b

instance PatchMPSAt 1 where
  patchMPSAtImpl s (MPS _ c r) = MPS s c r

instance PatchMPSAt 2 where
  patchMPSAtImpl s (MPS l _ r) = MPS l s r

instance PatchMPSAt 3 where
  patchMPSAtImpl s (MPS l c _) = MPS l c s

patchMPSAt
  :: forall i p b. (PatchMPSAt i, KnownNat b) => SiteAt 3 p b i -> MPS p b -> MPS p b
patchMPSAt = patchMPSAtImpl @i

class MPOAt (i :: Nat) where
  mpoSiteAtImpl :: forall p w. MPO p w -> OpSiteAt 3 p w i

instance MPOAt 1 where
  mpoSiteAtImpl (MPO o1 _ _) = o1

instance MPOAt 2 where
  mpoSiteAtImpl (MPO _ o2 _) = o2

instance MPOAt 3 where
  mpoSiteAtImpl (MPO _ _ o3) = o3

mpoSiteAt :: forall i p w. MPOAt i => MPO p w -> OpSiteAt 3 p w i
mpoSiteAt = mpoSiteAtImpl @i
