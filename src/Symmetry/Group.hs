{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}

-- | Shared group index for representation spines (@'Rep'@ / @'Irreps'@).
--
-- Fused Hom / intertwiners live in 'Hom' ('HomFused' / 'HomInter'), indexed by
-- @g :: Group@.
module Symmetry.Group
  ( Group (..)
  , Irreps
  , Rep
  , IrrepDim
  ) where

import Data.Kind (Type)
import GHC.TypeLits (Nat, type (+))
import Symmetry.Utils (Z)

data Group = U1 | SU2

type family Irreps (g :: Group) :: Type where
  Irreps U1 = Z
  Irreps SU2 = Nat

type family Rep (g :: Group) :: Type where
  Rep U1 = [(Z, Nat)]
  Rep SU2 = [(Nat, Nat)]

-- | Carrier dimension of a simple. U(1) charges are 1-dimensional; SU(2) uses @j+1@.
type family IrrepDim (g :: Group) (j :: Irreps g) :: Nat where
  IrrepDim U1 _ = 1
  IrrepDim SU2 j = j + 1
