{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}

-- | Shared group index for representation spines (@'Rep'@ / @'Irreps'@).
--
-- Fused Hom / intertwiners live in 'Hom' ('HomFused' / 'HomInter'), not as
-- block-sparse @Rep@ sector lists.
module Symmetry.Group
  ( Group (..)
  , Irreps
  , Rep
  ) where

import Data.Kind (Type)
import GHC.TypeLits (Nat)
import Symmetry.Utils (Z)

data Group = U1 | SU2

type family Irreps (g :: Group) :: Type where
  Irreps U1 = Z
  Irreps SU2 = Nat

type family Rep (g :: Group) :: Type where
  Rep U1 = [(Z, Nat)]
  Rep SU2 = [(Nat, Nat)]
