{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

-- | Indexing into open-boundary 'MPS' / 'MPO' from "TensorNetwork.MPS.General".
--
-- Sites are 1-based: @1@ = left, @2 .. n+1@ = bulk, @n+2@ = right.
-- Orthogonality-center positions use 'CenterPos' (@CenterBulk@ indexes
-- '_mpsBulk' via 'Finite n').
module TensorNetwork.DMRG.Chain
  ( chainLength
  , CenterPos (..)
  , centerPos
  , bulkCount
  , getBulk
  ) where

import GHC.TypeLits (KnownNat, Nat)
import Linear.V (V (..))
import Control.Lens (Ixed (ix), (^?))
import Data.Finite (packFinite)
import Data.Maybe (fromMaybe)
import TensorNetwork.MPS.General (CenterPos (..))
import TensorNetwork.Categorical.Props (cdim)

-- | Total sites: left + bulk + right.
chainLength :: forall (n :: Nat). KnownNat n => Int
chainLength = cdim @n + 2

-- | Number of bulk sites (@n@).
bulkCount :: forall (n :: Nat). KnownNat n => Int
bulkCount = cdim @n

-- | Map a 1-based site index to a 'CenterPos n'.
centerPos :: forall (n :: Nat). KnownNat n => Int -> CenterPos n
centerPos i
  | i == 1 = CenterLeft
  | i == chainLength @n = CenterRight
  | i >= 2 && i <= bulkCount @n + 1 =
      case packFinite @n (fromIntegral (i - 2)) of
        Just j -> CenterBulk j
        Nothing ->
          error $
            "centerPos: bulk index "
              ++ show (i - 2)
              ++ " out of range for n = "
              ++ show (bulkCount @n)
  | otherwise =
      error $
        "centerPos: index "
          ++ show i
          ++ " out of range 1.."
          ++ show (chainLength @n)

getBulk :: forall (n :: Nat) a. KnownNat n => Int -> V n a -> a
getBulk j (V v) = fromMaybe (error "bad index") (v ^? ix j)
