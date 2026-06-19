{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Singleton-indexed site / operator / environment types for open-boundary
-- 'MPS' / 'MPO' chains.
--
-- Phase 0 spike: type families reduce under 'sNatEq' witnesses (not under
-- abstract @i@). See 'getSiteSing', 'setSiteSing', 'solveCentreSing'.
module TensorNetwork.DMRG.SiteIndex
  ( -- * Chain length
    ChainEnd
    -- * Type-level site / operator / environment types
  , SiteAt
  , OpSiteAt
  , LeftEnvAt
  , RightEnvAt
    -- * Singleton-indexed accessors
  , getSiteSing
  , setSiteSing
  , getOpSing
  , setOpSing
  , solveCentreSing
    -- * Properties (Phase 0 spike)
  , prop_getSiteSingMatchesGetSite
  , prop_setSiteSingRoundTrip
  , prop_solveCentreSingMatchesSolveCentre
  ) where

import Prelude
import Data.List (splitAt)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import Data.Kind (Type)
import Data.Singletons (SingI, sing)
import Data.Vector.Sized (Vector, fromList, toList)
import GHC.TypeLits (KnownNat, Nat, type (+), type (*), natVal)
import Math.LinearMap.Category (getLinearMap, LinearMap (..))
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (Sized (extract))
import Symmetry.ChargeEq (NatEq, NatEqResult (..), sNatEq)
import TensorNetwork.DMRG.Chain (getSite, SomeSite (..))
import TensorNetwork.DMRG.Env
  ( LeftEnv, RightEnv, extendLeft, extendRight, leftBoundary, rightBoundary )
import TensorNetwork.DMRG.Fixed3 (effectiveH, solveCentre)
import TensorNetwork.MPS.Fixed3 (genMPS222, genMPO222)
import TensorNetwork.MPS.Fixed3.Internal
  ( Site (..), OpSite (..), MPS (..), MPO (..), withMPO3, withMPS3 )
import qualified Test.QuickCheck as QC

--------------------------------------------------------------------------------
-- Type families
--------------------------------------------------------------------------------

type ChainEnd l = l + 2

type family If (b :: Bool) t f where
  If 'True t f = t
  If 'False t f = f

-- | MPS site type at 1-based index @i@ on a chain with @l@ bulk sites.
--
-- All branches use @If (NatEq ...)@ so reduction follows @sNatEq@ witnesses
-- (@i ~ 1@ alone is not enough for closed-family matching on @i@).
type family SiteAt (l :: Nat) (p :: Nat) (b :: Nat) (i :: Nat) :: Type where
  SiteAt l p b i =
    If (NatEq i 1)
      (Site 1 p b)
      (If (NatEq i (l + 2)) (Site b p 1) (Site b p b))

type family OpSiteAt (l :: Nat) (p :: Nat) (w :: Nat) (i :: Nat) :: Type where
  OpSiteAt l p w i =
    If (NatEq i 1)
      (OpSite 1 p w)
      (If (NatEq i (l + 2)) (OpSite w p 1) (OpSite w p w))

type family LeftEnvAt (l :: Nat) (w :: Nat) (b :: Nat) (i :: Nat) :: Type where
  LeftEnvAt l w b i =
    If (NatEq i 1) (LeftEnv 1 1 1) (LeftEnv w b b)

type family RightEnvAt (l :: Nat) (w :: Nat) (b :: Nat) (i :: Nat) :: Type where
  RightEnvAt l w b i =
    If (NatEq i 1)
      (RightEnv w b b)
      (If (NatEq i (l + 2)) (RightEnv 1 1 1) (RightEnv w b b))

--------------------------------------------------------------------------------
-- Vector helpers (mirror 'TensorNetwork.DMRG.Chain')
--------------------------------------------------------------------------------

bulkAt :: Int -> Vector l a -> a
bulkAt j v = toList v !! j

bulkUpdate :: forall l a. KnownNat l => Int -> a -> Vector l a -> Vector l a
bulkUpdate j x v =
  fromMaybe (error "SiteIndex.bulkUpdate: length mismatch") (fromList (pre ++ x : post))
  where
    (pre, _:post) = splitAt j (toList v)

bulkVecIndex :: forall i. KnownNat i => Int
bulkVecIndex = fromIntegral (natVal (Proxy @i)) - 2

--------------------------------------------------------------------------------
-- Singleton-indexed MPS / MPO accessors
--------------------------------------------------------------------------------

getSiteSing
  :: forall p b l i
   . ( KnownNat l, KnownNat (l + 2), KnownNat i, KnownNat p, KnownNat b, SingI i )
  => MPS p b l
  -> SiteAt l p b i
getSiteSing mps =
  case sNatEq (sing @i) (sing @1) of
    NatEqTrue -> siteL mps
    NatEqFalse ->
      case sNatEq (sing @i) (sing @(l + 2)) of
        NatEqTrue -> siteR mps
        NatEqFalse -> bulkAt (bulkVecIndex @i) (sitesC mps)

setSiteSing
  :: forall p b l i
   . ( KnownNat l, KnownNat (l + 2), KnownNat i, KnownNat p, KnownNat b, SingI i )
  => SiteAt l p b i
  -> MPS p b l
  -> MPS p b l
setSiteSing s mps =
  case sNatEq (sing @i) (sing @1) of
    NatEqTrue -> mps { siteL = s }
    NatEqFalse ->
      case sNatEq (sing @i) (sing @(l + 2)) of
        NatEqTrue -> mps { siteR = s }
        NatEqFalse ->
          mps { sitesC = bulkUpdate (bulkVecIndex @i) s (sitesC mps) }

getOpSing
  :: forall p w l i
   . ( KnownNat l, KnownNat (l + 2), KnownNat i, KnownNat p, KnownNat w, SingI i )
  => MPO p w l
  -> OpSiteAt l p w i
getOpSing mpo =
  case sNatEq (sing @i) (sing @1) of
    NatEqTrue -> opL mpo
    NatEqFalse ->
      case sNatEq (sing @i) (sing @(l + 2)) of
        NatEqTrue -> opR mpo
        NatEqFalse -> bulkAt (bulkVecIndex @i) (opsC mpo)

setOpSing
  :: forall p w l i
   . ( KnownNat l, KnownNat (l + 2), KnownNat i, KnownNat p, KnownNat w, SingI i )
  => OpSiteAt l p w i
  -> MPO p w l
  -> MPO p w l
setOpSing o mpo =
  case sNatEq (sing @i) (sing @1) of
    NatEqTrue -> mpo { opL = o }
    NatEqFalse ->
      case sNatEq (sing @i) (sing @(l + 2)) of
        NatEqTrue -> mpo { opR = o }
        NatEqFalse ->
          mpo { opsC = bulkUpdate (bulkVecIndex @i) o (opsC mpo) }

--------------------------------------------------------------------------------
-- Singleton-indexed local solve
--------------------------------------------------------------------------------

solveCentreSing
  :: forall p w b l i
   . ( KnownNat l, KnownNat (l + 2), KnownNat i
     , KnownNat p, KnownNat w, KnownNat b, SingI i
     )
  => LeftEnvAt l w b i
  -> OpSiteAt l p w i
  -> RightEnvAt l w b i
  -> SiteAt l p b i
  -> (Double, SiteAt l p b i)
solveCentreSing l op r centre =
  case sNatEq (sing @i) (sing @1) of
    NatEqTrue -> solveAtFirst @p @w @b @l l op r centre
    NatEqFalse ->
      case sNatEq (sing @i) (sing @(l + 2)) of
        NatEqTrue -> solveAtLast @p @w @b @l l op r centre
        NatEqFalse -> solveAtBulk @p @w @b @l l op r centre

solveAtFirst
  :: forall p w b l
   . ( KnownNat l, KnownNat p, KnownNat w, KnownNat b )
  => LeftEnv 1 1 1
  -> OpSite 1 p w
  -> RightEnv w b b
  -> Site 1 p b
  -> (Double, Site 1 p b)
solveAtFirst l op r (Site _centre) =
  let (e, c) = solveCentre (effectiveH @p l op r)
  in (e, Site c)

solveAtBulk
  :: forall p w b l
   . ( KnownNat l, KnownNat p, KnownNat w, KnownNat b )
  => LeftEnv w b b
  -> OpSite w p w
  -> RightEnv w b b
  -> Site b p b
  -> (Double, Site b p b)
solveAtBulk l op r (Site _centre) =
  let (e, c) = solveCentre (effectiveH @p l op r)
  in (e, Site c)

solveAtLast
  :: forall p w b l
   . ( KnownNat l, KnownNat p, KnownNat w, KnownNat b )
  => LeftEnv w b b
  -> OpSite w p 1
  -> RightEnv 1 1 1
  -> Site b p 1
  -> (Double, Site b p 1)
solveAtLast l op r (Site _centre) =
  let (e, c) = solveCentre (effectiveH @p l op r)
  in (e, Site c)

--------------------------------------------------------------------------------
-- QuickCheck oracles (3-site chain, @l ~ 1@)
--------------------------------------------------------------------------------

siteMapsEqual
  :: forall bl p br
   . ( KnownNat bl, KnownNat p, KnownNat br, KnownNat (p * br) )
  => Site bl p br -> Site bl p br -> QC.Property
siteMapsEqual (Site f) (Site g) =
  extract (getLinearMap f) QC.=== extract (getLinearMap g)

prop_getSiteSingMatchesGetSite :: QC.Property
prop_getSiteSingMatchesGetSite =
  QC.forAll genMPS222 $ \mps ->
    case getSite 1 mps of
      SiteLeft s -> siteMapsEqual s (getSiteSing @2 @2 @1 @1 mps)
      _ -> QC.property False
    QC..&&. case getSite 2 mps of
      SiteBulk s -> siteMapsEqual s (getSiteSing @2 @2 @1 @2 mps)
      _ -> QC.property False
    QC..&&. case getSite 3 mps of
      SiteRight s -> siteMapsEqual s (getSiteSing @2 @2 @1 @3 mps)
      _ -> QC.property False

prop_setSiteSingRoundTrip :: QC.Property
prop_setSiteSingRoundTrip =
  QC.forAll genMPS222 $ \mps ->
    siteMapsEqual
      (getSiteSing @2 @2 @1 @2 mps)
      (getSiteSing @2 @2 @1 @2 (setSiteSing @2 @2 @1 @2 (getSiteSing @2 @2 @1 @2 mps) mps))
      QC..&&. siteMapsEqual
        (getSiteSing @2 @2 @1 @1 mps)
        (getSiteSing @2 @2 @1 @1 (setSiteSing @2 @2 @1 @1 (getSiteSing @2 @2 @1 @1 mps) mps))
      QC..&&. siteMapsEqual
        (getSiteSing @2 @2 @1 @3 mps)
        (getSiteSing @2 @2 @1 @3 (setSiteSing @2 @2 @1 @3 (getSiteSing @2 @2 @1 @3 mps) mps))

prop_solveCentreSingMatchesSolveCentre :: QC.Property
prop_solveCentreSingMatchesSolveCentre =
  QC.forAll genMPS222 $ \psiY ->
  QC.forAll genMPO222 $ \mpo ->
    withMPS3 psiY $ \s1 y s3 ->
    withMPO3 mpo $ \o1 o2 o3 ->
      let l1 = extendLeft leftBoundary s1 o1 s1
          r3 = extendRight @2 s3 o3 s3 rightBoundary
          (eSing, cSing) = solveCentreSing @2 @2 @2 @1 @2 l1 o2 r3 y
          (eDirect, cDirect) = solveCentre (effectiveH @2 l1 o2 r3)
      in eSing QC.=== eDirect
           QC..&&. siteMapsEqual cSing (Site cDirect)
