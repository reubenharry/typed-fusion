{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Type-level site lists and bond indices for open-boundary MPS/MPO chains.
--
-- 'AllSites' builds the full site-type spine for an @n@-site chain; 'LeftSites'
-- and 'RightSites' split it at the DMRG centre index via 'Take' and 'Drop'.
module TensorNetwork.DMRG.SiteLists
  ( -- * Site membership
    IsFirstSite
  , IsLastSite
    -- * Bond dimensions at site @i@
  , LeftBond
  , RightBond
  , LeftMPOBond
  , RightMPOBond
    -- * Site and operator types at index @i@
  , SiteAt
  , OpSiteAt
    -- * Full chain and zipper spines
  , AllSites
  , LeftSites
  , RightSites
    -- * Type-level list utilities
  , Take
  , Drop
  ) where

import Data.Kind (Type)
import Data.Type.Bool (If)
import GHC.TypeLits (Nat, CmpNat, type (-))
import TensorNetwork.MPS.Fixed3.Internal (Site (..), OpSite (..))

-- | @True@ when @i@ is the first site of a chain.
type family IsFirstSite (i :: Nat) :: Bool where
  IsFirstSite 1 = 'True
  IsFirstSite _ = 'False

type family IsEqOrdering (o :: Ordering) :: Bool where
  IsEqOrdering 'EQ = 'True
  IsEqOrdering _ = 'False

-- | @True@ when @i@ is the last site (@i == n@).
type IsLastSite (n :: Nat) (i :: Nat) = IsEqOrdering (CmpNat i n)

-- | Incoming MPS bond at site @i@ (open left boundary is @1@).
type LeftBond (n :: Nat) (b :: Nat) (i :: Nat) = If (IsFirstSite i) 1 b

-- | Outgoing MPS bond at site @i@ (open right boundary is @1@).
type RightBond (n :: Nat) (b :: Nat) (i :: Nat) = If (IsLastSite n i) 1 b

-- | Incoming MPO bond at site @i@.
type LeftMPOBond (n :: Nat) (w :: Nat) (i :: Nat) = If (IsFirstSite i) 1 w

-- | Outgoing MPO bond at site @i@.
type RightMPOBond (n :: Nat) (w :: Nat) (i :: Nat) = If (IsLastSite n i) 1 w

-- | MPS site tensor at index @i@ in an @n@-site open-boundary chain.
type SiteAt (n :: Nat) (p :: Nat) (b :: Nat) (i :: Nat) =
  Site (LeftBond n b i) p (RightBond n b i)

-- | MPO operator at index @i@.
type OpSiteAt (n :: Nat) (p :: Nat) (w :: Nat) (i :: Nat) =
  OpSite (LeftMPOBond n w i) p (RightMPOBond n w i)

-- | Append one element to the end of a type-level list.
type family SnocList (xs :: [k]) (x :: k) :: [k] where
  SnocList '[] y = '[y]
  SnocList (z ': ys) x = z ': SnocList ys x

-- | Take the first @m@ elements of a type-level list.
type family Take (m :: Nat) (xs :: [k]) :: [k] where
  Take 0 _ = '[]
  Take _ '[] = '[]
  Take m (x ': xs) = x ': Take (m - 1) xs

-- | Drop the first @m@ elements of a type-level list.
type family Drop (m :: Nat) (xs :: [k]) :: [k] where
  Drop 0 xs = xs
  Drop _ '[] = '[]
  Drop m (_ ': xs) = Drop (m - 1) xs

-- | All MPS site types for an @n@-site chain, ordered from site @1@ to site @n@.
--
-- Each 'SiteAt' uses the full chain length @n@ for open-boundary bonds, even
-- while building the prefix recursively.
type family AllSites (n :: Nat) (p :: Nat) (b :: Nat) :: [Type] where
  AllSites 0 _ _ = '[]
  AllSites n p b = AllSitesUpTo n p b n

-- | Sites @1 .. i@ of an @n@-site chain.
type family AllSitesUpTo (n :: Nat) (p :: Nat) (b :: Nat) (i :: Nat) :: [Type] where
  AllSitesUpTo n p b 1 = '[SiteAt n p b 1]
  AllSitesUpTo n p b i = SnocList (AllSitesUpTo n p b (i - 1)) (SiteAt n p b i)

-- | Sites strictly left of centre @i@.
type LeftSites (n :: Nat) (p :: Nat) (b :: Nat) (i :: Nat) =
  Take (i - 1) (AllSites n p b)

-- | Sites strictly right of centre @i@.
type RightSites (n :: Nat) (p :: Nat) (b :: Nat) (i :: Nat) =
  Drop i (AllSites n p b)
