{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

-- | General-length MPS/MPO storage and indexing.
module TensorNetwork.DMRG.Chain where

import Data.Finite (Finite, finite, getFinite, packFinite)
import GHC.TypeLits (KnownNat, Nat, natVal, type (+))
import Data.Proxy (Proxy (..))
import Data.Maybe (fromMaybe)
import Data.List (splitAt)
import Data.Vector.Sized (Vector, fromList, toList)

-- bulkAt :: Int -> Vector l a -> a
-- bulkAt j v = toList v !! j

-- bulkUpdate :: forall l a. KnownNat l => Int -> a -> Vector l a -> Vector l a
-- bulkUpdate j x v =
--   fromMaybe (error "bulkUpdate: length mismatch") (fromList (pre ++ x : post))
--   where
--     (pre, _:post) = splitAt j (toList v)

-- chainLength :: forall l. KnownNat l => Int
-- chainLength = fromIntegral (natVal (Proxy @l)) + 2

-- -- | Total number of sites on an open-boundary chain with @l@ bulk sites.
-- type ChainEnd l = l + 2

-- -- | Convert a 0-based 'Finite' cursor to the 1-based site index used by 'getSite'.
-- siteInt :: Finite (ChainEnd l) -> Int
-- siteInt c = fromIntegral (getFinite c) + 1

-- -- | Leftmost site (site @1@).
-- firstSite :: (KnownNat l, KnownNat (ChainEnd l)) => Finite (ChainEnd l)
-- firstSite = finite 0

-- advanceSite
--   :: (KnownNat l, KnownNat (ChainEnd l))
--   => Finite (ChainEnd l)
--   -> Maybe (Finite (ChainEnd l))
-- advanceSite c = packFinite (getFinite c + 1)

-- retreatSite
--   :: KnownNat (ChainEnd l)
--   => Finite (ChainEnd l)
--   -> Maybe (Finite (ChainEnd l))
-- retreatSite c = packFinite (getFinite c - 1)

-- isFirstSite :: Finite (ChainEnd l) -> Bool
-- isFirstSite c = getFinite c == 0

-- isLastSite :: forall l. KnownNat l => Finite (ChainEnd l) -> Bool
-- isLastSite c = siteInt c >= chainLength @l

-- data SomeSite p b where
--   SiteLeft  :: Site 1 p b -> SomeSite p b
--   SiteBulk  :: Site b p b -> SomeSite p b
--   SiteRight :: Site b p 1 -> SomeSite p b

-- data SomeOpSite p w where
--   OpLeft  :: OpSite 1 p w -> SomeOpSite p w
--   OpBulk  :: OpSite w p w -> SomeOpSite p w
--   OpRight :: OpSite w p 1 -> SomeOpSite p w

-- getSite
--   :: forall p b l
--    . KnownNat l
--   => Int
--   -> MPS p b l
--   -> SomeSite p b
-- getSite i mps
--   | i == 1 = SiteLeft (siteL mps)
--   | i == chainLength @l = SiteRight (siteR mps)
--   | i >= 2 && i <= chainLength @l - 1 = SiteBulk (bulkAt (i - 2) (sitesC mps))
--   | otherwise =
--       error ("getSite: index " ++ show i ++ " out of range 1.." ++ show (chainLength @l))

-- setSite
--   :: forall p b l
--    . KnownNat l
--   => Int
--   -> SomeSite p b
--   -> MPS p b l
--   -> MPS p b l
-- setSite 1 (SiteLeft s) mps = mps { siteL = s }
-- setSite i (SiteBulk s) mps
--   | i >= 2 && i <= chainLength @l - 1 =
--       mps { sitesC = bulkUpdate (i - 2) s (sitesC mps) }
--   | otherwise = siteIndexError @l "setSite" i
-- setSite i (SiteRight s) mps
--   | i == chainLength @l = mps { siteR = s }
--   | otherwise = siteIndexError @l "setSite" i
-- setSite i _ _ = siteIndexError @l "setSite" i

-- siteIndexError :: forall l a. KnownNat l => String -> Int -> a
-- siteIndexError what i =
--   error (what ++ ": index " ++ show i ++ " out of range 1.." ++ show (chainLength @l))

-- getOp
--   :: forall p w l
--    . KnownNat l
--   => Int
--   -> MPO p w l
--   -> SomeOpSite p w
-- getOp i mpo
--   | i == 1 = OpLeft (opL mpo)
--   | i == chainLength @l = OpRight (opR mpo)
--   | i >= 2 && i <= chainLength @l - 1 = OpBulk (bulkAt (i - 2) (opsC mpo))
--   | otherwise =
--       error ("getOp: index " ++ show i ++ " out of range 1.." ++ show (chainLength @l))

-- setOp
--   :: forall p w l
--    . KnownNat l
--   => Int
--   -> SomeOpSite p w
--   -> MPO p w l
--   -> MPO p w l
-- setOp 1 (OpLeft o) mpo = mpo { opL = o }
-- setOp i (OpBulk o) mpo
--   | i >= 2 && i <= chainLength @l - 1 =
--       mpo { opsC = bulkUpdate (i - 2) o (opsC mpo) }
--   | otherwise = siteIndexError @l "setOp" i
-- setOp i (OpRight o) mpo
--   | i == chainLength @l = mpo { opR = o }
--   | otherwise = siteIndexError @l "setOp" i
-- setOp i _ _ = siteIndexError @l "setOp" i
