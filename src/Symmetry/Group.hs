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
-- @g :: Group@. Group /elements/ are 'GroupElement'.
module Symmetry.Group
  ( Group (..)
  , Irreps
  , Rep
  , IrrepDim
  , GroupElement
  , U1Element (..)
  , u1Ident
  , u1FromAngle
  ) where

import Data.Kind (Type)
import GHC.TypeLits (Nat, type (+))
import Symmetry.SU2 (SU2Element)
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

-- | Concrete group element for representation actions.
type family GroupElement (g :: Group) :: Type where
  GroupElement SU2 = SU2Element
  GroupElement U1 = U1Element

-- | U(1) element as a phase angle @θ@ (radians): acts on charge @q@ by @e^{i q θ}@.
newtype U1Element = U1Element { u1Angle :: Double }
  deriving (Eq, Show)

-- | Identity (@θ = 0@).
u1Ident :: U1Element
u1Ident = U1Element 0

-- | Build from an angle in radians.
u1FromAngle :: Double -> U1Element
u1FromAngle = U1Element
