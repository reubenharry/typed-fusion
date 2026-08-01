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
module TensorNetwork.DMRG.Chain where

import GHC.TypeLits (KnownNat, Nat, natVal)
import Data.Proxy (Proxy (..))
import Data.Foldable (toList)
import qualified Data.Vector as Vector
import Linear.V (V (..))
import Control.Lens ((&), (.~), Ixed (ix), (^.), (^?))
import TensorNetwork.MPS.General
  ( MPS (..), LeftSite, BulkSite, RightSite, mpsLeft, mpsRight )
import Data.Maybe (fromMaybe)
import TensorNetwork.Categorical.Props (cdim)

-- | Number of bulk sites (@n@).
-- getNat :: forall (n :: Nat). KnownNat n => Int
-- getNat = fromIntegral (natVal (Proxy @n))

-- | Total sites: left + bulk + right.
chainLength :: forall (n :: Nat). KnownNat n => Int
chainLength = cdim @n + 2

-- | Which site a 1-based index refers to.
-- data CentrePos = CentreLeft | CentreBulk Int | CentreRight
--   deriving (Eq, Show)

-- centrePos :: forall (n :: Nat). KnownNat n => Int -> CentrePos
-- centrePos i
--   | i == 1 = CentreLeft
--   | i == chainLength @n = CentreRight
--   | i >= 2 && i <= getNat @n + 1 = CentreBulk (i - 2)
--   | otherwise = error ("centrePos: index " ++ show i ++ " out of range 1.." ++ show (chainLength @n))

getBulk :: forall (n :: Nat) a. KnownNat n => Int -> V n a -> a
getBulk j (V v) = fromMaybe (error "bad index") (v ^? ix j)
