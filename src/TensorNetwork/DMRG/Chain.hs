{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- | n-site MPS/MPO as typed heterogeneous chains, and zipper reassembly.
module TensorNetwork.DMRG.Chain
  ( -- * Chain types
    MPSn
  , MPOn
    -- * 3-site record bridge
  , mps3ToChain
  , mps3FromChain
  , mpo3ToChain
  , mpo3FromChain
    -- * Zipper assembly
  , assembleZipperSites
  , AssembleFromZipper (..)
    -- * Indexed updates on the 3-site record
  , PatchMPSAt (..)
  , patchMPSAt
  , MPOAt (..)
  , mpoSiteAt
  ) where

import Data.Kind (Type)
import GHC.TypeLits (Nat, KnownNat)
import TensorNetwork.DMRG.Spine (HList (..))
import TensorNetwork.DMRG.SiteLists
  ( AllSites, AllOpSites, LeftSites, RightSites, SiteAt, OpSiteAt
  , ZipperAssembled, Append )
import TensorNetwork.MPS.Fixed3.Internal (MPS (..), MPO (..))

-- | An @n@-site open-boundary MPS as a typed site spine.
type MPSn n p b = HList (AllSites n p b)

-- | An @n@-site open-boundary MPO as a typed operator spine.
type MPOn n p w = HList (AllOpSites n p w)

class AppendHList (xs :: [Type]) (ys :: [Type]) where
  appendHList :: HList xs -> HList ys -> HList (Append xs ys)

instance AppendHList '[] ys where
  appendHList HNil ys = ys

instance AppendHList xs ys => AppendHList (x ': xs) ys where
  appendHList (x :& xs') ys = x :& appendHList xs' ys

-- | Reassemble the full site chain from a DMRG zipper at centre @i@.
assembleZipperSites
  :: forall n p b i
   . ( ZipperAssembled n p b i ~ AllSites n p b
     , AppendHList (LeftSites n p b i) '[SiteAt n p b i]
     , AppendHList
         (Append (LeftSites n p b i) '[SiteAt n p b i])
         (RightSites n p b i)
     )
  => HList (LeftSites n p b i)
  -> SiteAt n p b i
  -> HList (RightSites n p b i)
  -> MPSn n p b
assembleZipperSites ls centre rs =
  appendHList (appendHList ls (centre :& HNil)) rs

-- | Assemble a zipper at a known centre index (needed when @i@ is not concrete).
class AssembleFromZipper (i :: Nat) where
  assembleZipper
    :: forall p b. KnownNat b
    => HList (LeftSites 3 p b i)
    -> SiteAt 3 p b i
    -> HList (RightSites 3 p b i)
    -> MPSn 3 p b

instance AssembleFromZipper 1 where
  assembleZipper
    :: forall p b. KnownNat b
    => HList (LeftSites 3 p b 1)
    -> SiteAt 3 p b 1
    -> HList (RightSites 3 p b 1)
    -> MPSn 3 p b
  assembleZipper ls c rs = assembleZipperSites @3 @p @b @1 ls c rs

instance AssembleFromZipper 2 where
  assembleZipper
    :: forall p b. KnownNat b
    => HList (LeftSites 3 p b 2)
    -> SiteAt 3 p b 2
    -> HList (RightSites 3 p b 2)
    -> MPSn 3 p b
  assembleZipper ls c rs = assembleZipperSites @3 @p @b @2 ls c rs

instance AssembleFromZipper 3 where
  assembleZipper
    :: forall p b. KnownNat b
    => HList (LeftSites 3 p b 3)
    -> SiteAt 3 p b 3
    -> HList (RightSites 3 p b 3)
    -> MPSn 3 p b
  assembleZipper ls c rs = assembleZipperSites @3 @p @b @3 ls c rs

mps3ToChain :: MPS p b -> MPSn 3 p b
mps3ToChain (MPS s1 s2 s3) = s1 :& s2 :& s3 :& HNil

mps3FromChain :: MPSn 3 p b -> MPS p b
mps3FromChain (s1 :& s2 :& s3 :& HNil) = MPS s1 s2 s3

mpo3ToChain :: MPO p w -> MPOn 3 p w
mpo3ToChain (MPO o1 o2 o3) = o1 :& o2 :& o3 :& HNil

mpo3FromChain :: MPOn 3 p w -> MPO p w
mpo3FromChain (o1 :& o2 :& o3 :& HNil) = MPO o1 o2 o3

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
