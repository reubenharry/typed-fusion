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
{-# LANGUAGE RecordWildCards #-}

-- | Singleton-indexed DMRG zipper (Phase 1: @l ~ 1@, centre @i@ in the type).
--
-- Chain storage remains 'MPS' / 'MPO'. Centre site / env types come from
-- 'TensorNetwork.DMRG.SiteIndex'. Move and solve operations are monomorphic
-- per site index (@1@, @2@, @3@) because GHC does not rewrite @i + 1@ from
-- 'NatEq' witnesses alone; Phase 2 will generalise bulk indices and @l@.
--
-- The legacy value-level 'TensorNetwork.DMRG.Fixed3.MPSZipper' remains for
-- sweep loops until Phase 3.
module TensorNetwork.DMRG.Zipper
  ( MPSZipper (..)
  , toZipper
  , moveRight1
  , moveRight2
  , moveLeft2
  , moveLeft3
  , solveCenterAt1
  , solveCenterAt2
  , centreEnergy1
  , centreEnergy2
    -- * Properties (Phase 1, @l ~ 1@)
  , prop_toZipperMatchesLegacy
  , prop_moveRightMatchesLegacy
  , prop_moveLeftMatchesLegacy
  , prop_solveCenterAtMatchesLegacy
  , prop_centreEnergyMatchesLegacy
  ) where

import Prelude
import Data.Proxy (Proxy (..))
import Data.Kind (Type)
import Data.Singletons (SingI, sing)
import GHC.TypeLits (KnownNat, Nat, type (+), type (-), type (*), natVal)
import Math.LinearMap.Category (getLinearMap, LinearMap (..))
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (Sized (extract))
import Symmetry.ChargeEq (NatEqResult (..), sNatEq)
import TensorNetwork.DMRG.Env
  ( leftBoundary, rightBoundary, buildRightEnvFromSite, bulkLeftEnvUpTo
  , extendLeft, extendRight
  , LeftEnvAtCentre (..), RightEnvAtCentre (..) )
import qualified TensorNetwork.DMRG.Fixed3 as Legacy
  ( MPSZipper (..), effectiveH, solveCentre, departLeft, departRight
  , rightGaugeMPS, toZipper, moveRight, moveLeft, solveCenterAt, centreEnergy )
import TensorNetwork.DMRG.SiteIndex
  ( ChainEnd, SiteAt, OpSiteAt, LeftEnvAt, RightEnvAt
  , getSiteSing, setSiteSing, getOpSing, solveCentreSing )
import TensorNetwork.MPS.Fixed3 (genMPS222, genMPO222)
import TensorNetwork.MPS.Fixed3.Internal
  ( Site (..), MPS (..), MPO (..), withMPS3 )
import qualified Test.QuickCheck as QC

type family SuccSite (i :: Nat) :: Nat where
  SuccSite 1 = 2
  SuccSite 2 = 3

type family PredSite (i :: Nat) :: Nat where
  PredSite 2 = 1
  PredSite 3 = 2

data MPSZipper p b w l i = MPSZipper
  { theMPO :: MPO p w l
  , theMPS :: MPS p b l
  , leftEnv :: LeftEnvAt l w b i
  , rightEnv :: RightEnvAt l w b i
  }

--------------------------------------------------------------------------------
-- Environment updates (singleton-indexed)
--------------------------------------------------------------------------------

extendLeftEnvMoveRight
  :: forall p w b l i
   . ( KnownNat l, KnownNat (l + 2), KnownNat i, KnownNat (SuccSite i)
     , KnownNat p, KnownNat w, KnownNat b, SingI i, SingI (SuccSite i)
     )
  => LeftEnvAt l w b i
  -> SiteAt l p b i
  -> OpSiteAt l p w i
  -> LeftEnvAt l w b (SuccSite i)
extendLeftEnvMoveRight lft cn op =
  case sNatEq (sing @i) (sing @1) of
    NatEqTrue ->
      let env = extendLeft lft cn op cn
      in case sNatEq (sing @(SuccSite i)) (sing @1) of
           NatEqTrue -> error "extendLeftEnvMoveRight: unreachable"
           NatEqFalse -> env
    NatEqFalse ->
      case sNatEq (sing @i) (sing @(l + 2)) of
        NatEqTrue -> error "extendLeftEnvMoveRight: at right boundary"
        NatEqFalse ->
          let env = extendLeft lft cn op cn
          in case sNatEq (sing @(SuccSite i)) (sing @1) of
               NatEqTrue -> error "extendLeftEnvMoveRight: unreachable"
               NatEqFalse -> env

extendRightEnvMoveLeft
  :: forall p w b l i
   . ( KnownNat l, KnownNat (l + 2), KnownNat i, KnownNat (PredSite i)
     , KnownNat p, KnownNat w, KnownNat b, SingI i, SingI (PredSite i)
     )
  => SiteAt l p b i
  -> OpSiteAt l p w i
  -> RightEnvAt l w b i
  -> RightEnvAt l w b (PredSite i)
extendRightEnvMoveLeft cn op r =
  case sNatEq (sing @i) (sing @1) of
    NatEqTrue -> error "extendRightEnvMoveLeft: at left boundary"
    NatEqFalse ->
      case sNatEq (sing @i) (sing @(l + 2)) of
        NatEqTrue ->
          let env = extendRight cn op cn r
          in case sNatEq (sing @(PredSite i)) (sing @1) of
               NatEqTrue -> error "extendRightEnvMoveLeft: unreachable"
               NatEqFalse ->
                 case sNatEq (sing @(PredSite i)) (sing @(l + 2)) of
                   NatEqTrue -> error "extendRightEnvMoveLeft: unreachable"
                   NatEqFalse -> env
        NatEqFalse ->
          let env = extendRight cn op cn r
          in case sNatEq (sing @(PredSite i)) (sing @1) of
               NatEqTrue -> env
               NatEqFalse ->
                 case sNatEq (sing @(PredSite i)) (sing @(l + 2)) of
                   NatEqTrue -> error "extendRightEnvMoveLeft: unreachable"
                   NatEqFalse -> env

updateRightEnvMoveRight
  :: forall p w b l i
   . ( KnownNat l, KnownNat (l + 2), KnownNat i, KnownNat (SuccSite i), KnownNat (i + 2)
     , KnownNat p, KnownNat w, KnownNat b, SingI i, SingI (SuccSite i)
     )
  => MPO p w l
  -> MPS p b l
  -> RightEnvAt l w b i
  -> RightEnvAt l w b (SuccSite i)
updateRightEnvMoveRight mpo mps _r =
  case sNatEq (sing @(SuccSite i)) (sing @(l + 2)) of
    NatEqTrue ->
      case sNatEq (sing @(SuccSite i)) (sing @1) of
        NatEqTrue -> error "updateRightEnvMoveRight: unreachable"
        NatEqFalse ->
          case sNatEq (sing @(SuccSite i)) (sing @(l + 2)) of
            NatEqTrue -> rightBoundary
            NatEqFalse -> error "updateRightEnvMoveRight: unreachable"
    NatEqFalse ->
      let env =
            buildRightEnvFromSite (fromIntegral (natVal (Proxy @(i + 2)))) mpo mps
      in case sNatEq (sing @(SuccSite i)) (sing @1) of
           NatEqTrue -> error "updateRightEnvMoveRight: unreachable"
           NatEqFalse ->
             case sNatEq (sing @(SuccSite i)) (sing @(l + 2)) of
               NatEqTrue -> error "updateRightEnvMoveRight: unreachable"
               NatEqFalse -> env

updateLeftEnvMoveLeft
  :: forall p w b l i
   . ( KnownNat l, KnownNat (l + 2), KnownNat i, KnownNat (PredSite i)
     , KnownNat p, KnownNat w, KnownNat b, SingI i, SingI (PredSite i)
     )
  => MPO p w l
  -> MPS p b l
  -> LeftEnvAt l w b i
  -> LeftEnvAt l w b (PredSite i)
updateLeftEnvMoveLeft mpo mps _l =
  case sNatEq (sing @(PredSite i)) (sing @1) of
    NatEqTrue -> leftBoundary
    NatEqFalse ->
      let env = bulkLeftEnvUpTo (fromIntegral (natVal (Proxy @(PredSite i)))) mpo mps
      in case sNatEq (sing @(PredSite i)) (sing @(l + 2)) of
           NatEqTrue -> error "updateLeftEnvMoveLeft: unreachable"
           NatEqFalse -> env

departSiteLeftSing
  :: forall p b l i
   . ( KnownNat l, KnownNat (l + 2), KnownNat i
     , KnownNat p, KnownNat b
     , KnownNat (p * b), KnownNat (b * p), p * b ~ b * p
     , SingI i
     )
  => SiteAt l p b i -> SiteAt l p b i
departSiteLeftSing s =
  case sNatEq (sing @i) (sing @1) of
    NatEqTrue -> Legacy.departLeft s
    NatEqFalse ->
      case sNatEq (sing @i) (sing @(l + 2)) of
        NatEqTrue -> error "departSiteLeftSing: right-end site"
        NatEqFalse -> Legacy.departLeft s

departSiteRightSing
  :: forall p b l i
   . ( KnownNat l, KnownNat (l + 2), KnownNat i
     , KnownNat p, KnownNat b, KnownNat (p * b)
     , SingI i
     )
  => SiteAt l p b i -> SiteAt l p b i
departSiteRightSing s =
  case sNatEq (sing @i) (sing @1) of
    NatEqTrue -> error "departSiteRightSing: left-end site"
    NatEqFalse ->
      case sNatEq (sing @i) (sing @(l + 2)) of
        NatEqTrue -> Legacy.departRight s
        NatEqFalse -> Legacy.departRight s

--------------------------------------------------------------------------------
-- Zipper operations
--------------------------------------------------------------------------------

toZipper
  :: forall p w b
   . ( KnownNat (p * b), KnownNat (b * p), p * b ~ b * p
     , KnownNat p, KnownNat w, KnownNat b
     )
  => MPO p w 1
  -> MPS p b 1
  -> MPSZipper p b w 1 1
toZipper mpo mps =
  let mps' = Legacy.rightGaugeMPS mps
      rEnv = buildRightEnvFromSite 2 mpo mps'
  in MPSZipper mpo mps' leftBoundary rEnv

moveRight1
  :: forall p w b
   . ( KnownNat p, KnownNat w, KnownNat b
     , KnownNat (p * b), KnownNat (b * p), p * b ~ b * p
     )
  => MPSZipper p b w 1 1 -> MPSZipper p b w 1 2
moveRight1 MPSZipper{theMPO = mpo, theMPS = mps, leftEnv = lft, rightEnv = r} =
  let cn = departSiteLeftSing @p @b @1 @1 (getSiteSing @p @b @1 @1 mps)
      mps' = setSiteSing @p @b @1 @1 cn mps
      lft' = extendLeftEnvMoveRight @p @w @b @1 @1 lft cn (getOpSing @p @w @1 @1 mpo)
      r' = updateRightEnvMoveRight @p @w @b @1 @1 mpo mps' r
  in MPSZipper mpo mps' lft' r'

moveRight2
  :: forall p w b
   . ( KnownNat p, KnownNat w, KnownNat b
     , KnownNat (p * b), KnownNat (b * p), p * b ~ b * p
     )
  => MPSZipper p b w 1 2 -> MPSZipper p b w 1 3
moveRight2 MPSZipper{theMPO = mpo, theMPS = mps, leftEnv = lft, rightEnv = r} =
  let cn = departSiteLeftSing @p @b @1 @2 (getSiteSing @p @b @1 @2 mps)
      mps' = setSiteSing @p @b @1 @2 cn mps
      lft' = extendLeftEnvMoveRight @p @w @b @1 @2 lft cn (getOpSing @p @w @1 @2 mpo)
      r' = updateRightEnvMoveRight @p @w @b @1 @2 mpo mps' r
  in MPSZipper mpo mps' lft' r'

moveLeft2
  :: forall p w b
   . ( KnownNat p, KnownNat w, KnownNat b
     , KnownNat (p * b), KnownNat (b * p), p * b ~ b * p
     )
  => MPSZipper p b w 1 2 -> MPSZipper p b w 1 1
moveLeft2 MPSZipper{theMPO = mpo, theMPS = mps, leftEnv = lft, rightEnv = r} =
  let cn = departSiteRightSing @p @b @1 @2 (getSiteSing @p @b @1 @2 mps)
      mps' = setSiteSing @p @b @1 @2 cn mps
      r' = extendRightEnvMoveLeft @p @w @b @1 @2 cn (getOpSing @p @w @1 @2 mpo) r
      lft' = updateLeftEnvMoveLeft @p @w @b @1 @2 mpo mps' lft
  in MPSZipper mpo mps' lft' r'

moveLeft3
  :: forall p w b
   . ( KnownNat p, KnownNat w, KnownNat b
     , KnownNat (p * b), KnownNat (b * p), p * b ~ b * p
     )
  => MPSZipper p b w 1 3 -> MPSZipper p b w 1 2
moveLeft3 MPSZipper{theMPO = mpo, theMPS = mps, leftEnv = lft, rightEnv = r} =
  let cn = departSiteRightSing @p @b @1 @3 (getSiteSing @p @b @1 @3 mps)
      mps' = setSiteSing @p @b @1 @3 cn mps
      r' = extendRightEnvMoveLeft @p @w @b @1 @3 cn (getOpSing @p @w @1 @3 mpo) r
      lft' = updateLeftEnvMoveLeft @p @w @b @1 @3 mpo mps' lft
  in MPSZipper mpo mps' lft' r'

solveCenterAt1
  :: forall p w b
   . (KnownNat p, KnownNat w, KnownNat b)
  => MPSZipper p b w 1 1 -> MPSZipper p b w 1 1
solveCenterAt1 z@MPSZipper{theMPS = mps, theMPO = mpo, leftEnv = lft, rightEnv = r} =
  let (_, c) =
        solveCentreSing @p @w @b @1 @1 lft (getOpSing @p @w @1 @1 mpo) r
          (getSiteSing @p @b @1 @1 mps)
  in z { theMPS = setSiteSing @p @b @1 @1 c mps }

solveCenterAt2
  :: forall p w b
   . (KnownNat p, KnownNat w, KnownNat b)
  => MPSZipper p b w 1 2 -> MPSZipper p b w 1 2
solveCenterAt2 z@MPSZipper{theMPS = mps, theMPO = mpo, leftEnv = lft, rightEnv = r} =
  let (_, c) =
        solveCentreSing @p @w @b @1 @2 lft (getOpSing @p @w @1 @2 mpo) r
          (getSiteSing @p @b @1 @2 mps)
  in z { theMPS = setSiteSing @p @b @1 @2 c mps }

centreEnergy1
  :: forall p w b. (KnownNat p, KnownNat w, KnownNat b)
  => MPSZipper p b w 1 1 -> Double
centreEnergy1 MPSZipper{theMPO = mpo, leftEnv = lft, rightEnv = r} =
  fst (Legacy.solveCentre (Legacy.effectiveH @p lft (getOpSing @p @w @1 @1 mpo) r))

centreEnergy2
  :: forall p w b. (KnownNat p, KnownNat w, KnownNat b)
  => MPSZipper p b w 1 2 -> Double
centreEnergy2 MPSZipper{theMPO = mpo, leftEnv = lft, rightEnv = r} =
  fst (Legacy.solveCentre (Legacy.effectiveH @p lft (getOpSing @p @w @1 @2 mpo) r))

--------------------------------------------------------------------------------
-- Legacy comparison helpers (tests)
--------------------------------------------------------------------------------

centreIndexOf :: forall i. KnownNat i => Int
centreIndexOf = fromIntegral (natVal (Proxy @i))

toLegacy
  :: forall p b w l i
   . (KnownNat i, KnownNat l, KnownNat (l + 2), SingI i)
  => MPSZipper p b w l i -> Legacy.MPSZipper p b w l
toLegacy MPSZipper{..} =
  Legacy.MPSZipper
    theMPO
    theMPS
    (centreIndexOf @i)
    (leftEnvToLegacy @l @w @b @i leftEnv)
    (rightEnvToLegacy @l @w @b @i rightEnv)

leftEnvToLegacy
  :: forall l w b i
   . (KnownNat l, KnownNat (l + 2), SingI i)
  => LeftEnvAt l w b i -> LeftEnvAtCentre w b
leftEnvToLegacy lft =
  case sNatEq (sing @i) (sing @1) of
    NatEqTrue -> LeftEnvFirst lft
    NatEqFalse -> LeftEnvBulk lft

rightEnvToLegacy
  :: forall l w b i
   . (KnownNat l, KnownNat (l + 2), SingI i)
  => RightEnvAt l w b i -> RightEnvAtCentre w b
rightEnvToLegacy r =
  case sNatEq (sing @i) (sing @1) of
    NatEqTrue -> RightEnvBulk r
    NatEqFalse ->
      case sNatEq (sing @i) (sing @(l + 2)) of
        NatEqTrue ->
          case sNatEq (sing @i) (sing @1) of
            NatEqTrue -> error "rightEnvToLegacy: unreachable"
            NatEqFalse ->
              case sNatEq (sing @i) (sing @(l + 2)) of
                NatEqTrue -> RightEnvLast r
                NatEqFalse -> error "rightEnvToLegacy: unreachable"
        NatEqFalse -> RightEnvBulk r

siteMapsEqual
  :: forall bl p br
   . ( KnownNat bl, KnownNat p, KnownNat br, KnownNat (p * br) )
  => Site bl p br -> Site bl p br -> QC.Property
siteMapsEqual (Site f) (Site g) =
  extract (getLinearMap f) QC.=== extract (getLinearMap g)

mpsSitesEqual
  :: (KnownNat p, KnownNat b, KnownNat (p * b))
  => MPS3 p b -> MPS3 p b -> QC.Property
mpsSitesEqual m1 m2 =
  withMPS3 m1 $ \a b c ->
  withMPS3 m2 $ \a' b' c' ->
    siteMapsEqual a a'
    QC..&&. siteMapsEqual b b'
    QC..&&. siteMapsEqual c c'

type MPS3 p b = MPS p b 1

prop_toZipperMatchesLegacy :: QC.Property
prop_toZipperMatchesLegacy =
  QC.forAll genMPS222 $ \mps ->
  QC.forAll genMPO222 $ \mpo ->
    let z = toZipper @2 @2 @2 mpo mps
        z' = Legacy.toZipper mpo mps
    in centreIndexOf @1 QC.=== 1
       QC..&&. mpsSitesEqual (theMPS z) (Legacy.theMPS z')
       QC..&&. centreIndexOf @1 QC.=== Legacy.centreIndex z'

prop_moveRightMatchesLegacy :: QC.Property
prop_moveRightMatchesLegacy =
  QC.forAll genMPS222 $ \mps ->
  QC.forAll genMPO222 $ \mpo ->
    let z0 = toZipper @2 @2 @2 mpo mps
        z1 = moveRight1 @2 @2 @2 z0
        l0 = Legacy.toZipper mpo mps
        l1 = Legacy.moveRight l0
    in centreIndexOf @2 QC.=== 2
       QC..&&. mpsSitesEqual (theMPS z1) (Legacy.theMPS l1)
       QC..&&. centreIndexOf @2 QC.=== Legacy.centreIndex l1

prop_moveLeftMatchesLegacy :: QC.Property
prop_moveLeftMatchesLegacy =
  QC.forAll genMPS222 $ \mps ->
  QC.forAll genMPO222 $ \mpo ->
    let z0 = moveRight1 @2 @2 @2 (toZipper @2 @2 @2 mpo mps)
        z1 = moveLeft2 @2 @2 @2 z0
        l0 = Legacy.moveRight (Legacy.toZipper mpo mps)
        l1 = Legacy.moveLeft l0
    in centreIndexOf @1 QC.=== 1
       QC..&&. mpsSitesEqual (theMPS z1) (Legacy.theMPS l1)
       QC..&&. centreIndexOf @1 QC.=== Legacy.centreIndex l1

prop_solveCenterAtMatchesLegacy :: QC.Property
prop_solveCenterAtMatchesLegacy =
  QC.forAll genMPS222 $ \mps ->
  QC.forAll genMPO222 $ \mpo ->
    let z = solveCenterAt1 @2 @2 @2 (toZipper @2 @2 @2 mpo mps)
        legacyZ = Legacy.solveCenterAt (Legacy.toZipper mpo mps)
    in mpsSitesEqual (theMPS z) (Legacy.theMPS legacyZ)

prop_centreEnergyMatchesLegacy :: QC.Property
prop_centreEnergyMatchesLegacy =
  QC.forAll genMPS222 $ \mps ->
  QC.forAll genMPO222 $ \mpo ->
    let z = toZipper @2 @2 @2 mpo mps
        l = Legacy.toZipper mpo mps
    in centreEnergy1 @2 @2 @2 z QC.=== Legacy.centreEnergy l
       QC..&&. centreEnergy2 @2 @2 @2 (moveRight1 @2 @2 @2 z)
               QC.=== Legacy.centreEnergy (Legacy.moveRight l)
