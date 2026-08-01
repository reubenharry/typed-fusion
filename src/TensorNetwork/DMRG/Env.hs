{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}

-- | MPS–MPO environments for DMRG on "TensorNetwork.MPS.General".
module TensorNetwork.DMRG.Env
  ( LeftMPOEnv
  , RightMPOEnv
  , leftEnvAfterLeft
  , leftEnvBeforeBulk
  , leftEnvBeforeRight
  , rightEnvAfterRight
  , extendRightBulk
  , rightEnvAfterBulk
  , rightEnvAfterLeft
  ) where

import Prelude hiding (($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import qualified Control.Functor.Constrained as CF
import Control.Arrow.Constrained (($))
import Math.LinearMap.Category
  ( type (+>), type (⊗), TensorSpace (..), contractTensorMap, (-+$>), transposeTensor )
import Math.LinearMap.Coercion (curryLinearMap, (-+$=>))
import Data.Foldable (toList)
import GHC.TypeLits (KnownNat, Nat)
import Control.Lens ((^.))
import TensorNetwork.MPS.General
  ( FullNorm, MPS (..), MPO (..)
  , LeftMPOEnv, RightMPOEnv, BulkSite
  , leftMPOEnv, rightMPOEnv
  , transferMPOBulkSite, opWire, siteDagger
  , MPSConstraints, SiteDagger
  , mpsLeft, mpsBulk, mpsRight, mpoLeft, mpoBulk, mpoRight
  )
import TensorNetwork.Categorical.Props (cdim)

-- | Left environment after the left boundary (bra = ket = current MPS).
leftEnvAfterLeft
  :: MPSConstraints bond phys =>
  FullNorm bond -> FullNorm phys ->
  MPS bond phys n -> MPO bond n phys phys -> LeftMPOEnv bond
leftEnvAfterLeft nb np mps mpo =
  leftMPOEnv nb np (mps ^. mpsLeft) (mpo ^. mpoLeft) (mps ^. mpsLeft)

-- | Left environment immediately before bulk site @j@ (0-based).
leftEnvBeforeBulk
  :: forall bond phys (n :: Nat).
  (MPSConstraints bond phys, KnownNat n, SiteDagger bond phys bond) =>
  FullNorm bond -> FullNorm phys ->
  Int -> MPS bond phys n -> MPO bond n phys phys -> LeftMPOEnv bond
leftEnvBeforeBulk nb np j mps mpo =
  foldl step (leftEnvAfterLeft nb np mps mpo) [0 .. j - 1]
  where
    bs = toList (mps ^. mpsBulk)
    os = toList (mpo ^. mpoBulk)
    step env k =
      transferMPOBulkSite nb np (bs !! k) (os !! k) (bs !! k) env

leftEnvBeforeRight
  :: forall bond phys (n :: Nat).
  (MPSConstraints bond phys, KnownNat n, SiteDagger bond phys bond) =>
  FullNorm bond -> FullNorm phys ->
  MPS bond phys n -> MPO bond n phys phys -> LeftMPOEnv bond
leftEnvBeforeRight nb np mps mpo =
  leftEnvBeforeBulk nb np (cdim @n) mps mpo

rightEnvAfterRight
  :: MPSConstraints bond phys =>
  FullNorm bond -> FullNorm phys ->
  MPS bond phys n -> MPO bond n phys phys -> RightMPOEnv bond
rightEnvAfterRight nb np mps mpo =
  rightMPOEnv nb np (mps ^. mpsRight) (mpo ^. mpoRight) (mps ^. mpsRight)

-- | Extend a right environment leftward through one bulk site (partial trace
-- over the physical leg). Same wiring as the archived 'extendRight'.
extendRightBulk
  :: forall bond phys.
  (MPSConstraints bond phys, SiteDagger bond phys bond) =>
  FullNorm bond -> FullNorm phys ->
  BulkSite bond phys ->
  ((bond ⊗ phys) +> (bond ⊗ phys)) ->
  BulkSite bond phys ->
  RightMPOEnv bond ->
  RightMPOEnv bond
extendRightBulk nb np bra op ket envR =
  CF.fmap (contractTensorMap Cat.. CF.fmap transposeTensor)
    -+$> (curryLinearMap -+$=> k)
  where
    k :: ((bond ⊗ bond) ⊗ phys) +> (bond ⊗ phys)
    k = siteDagger nb np nb bra . envR . opWire op ket

-- | Right environment immediately after bulk site @j@ (0-based): contracts
-- bulk sites @j+1 .. n-1@ and the right boundary.
rightEnvAfterBulk
  :: forall bond phys (n :: Nat).
  (MPSConstraints bond phys, KnownNat n, SiteDagger bond phys bond) =>
  FullNorm bond -> FullNorm phys ->
  Int -> MPS bond phys n -> MPO bond n phys phys -> RightMPOEnv bond
rightEnvAfterBulk nb np j mps mpo =
  foldr step (rightEnvAfterRight nb np mps mpo) [j + 1 .. cdim @n - 1]
  where
    bs = toList (mps ^. mpsBulk)
    os = toList (mpo ^. mpoBulk)
    step k env =
      extendRightBulk nb np (bs !! k) (os !! k) (bs !! k) env

-- | Right environment after the left boundary (all bulk + right contracted).
rightEnvAfterLeft
  :: forall bond phys (n :: Nat).
  (MPSConstraints bond phys, KnownNat n, SiteDagger bond phys bond) =>
  FullNorm bond -> FullNorm phys ->
  MPS bond phys n -> MPO bond n phys phys -> RightMPOEnv bond
rightEnvAfterLeft nb np =
  rightEnvAfterBulk nb np (-1)
