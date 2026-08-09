{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Group-indexed representation objects for the forgetful functor.
--
-- @'I@ is the monoidal unit (@C 1@); @'REP r@ is a reduced spine; @a ':⊗: b@
-- is the unfused external tensor product (not yet regrouped by total charge /
-- CG). Sector pairs are @m `IrrepOf` j@ (same as @'(j, m)@).
--
-- Note: infix data constructors must start with @:@, so the product is
-- @(:⊗:)@ rather than bare @⊗@ (which would also clash visually with the
-- vector-space operator from 'Math.LinearMap.Category').
module Symmetry.RepObj
  ( RepObj (..)
  , ToVector
  , type IrrepOf
  ) where

import Data.Kind (Type)
import GHC.TypeLits (Nat)
import Math.LinearMap.Category (type (⊗))
import Numeric.LinearAlgebra.Static (C)
import Symmetry.Group (Group, Rep, RepDimG)

-- | Object of the rep category: unit, reduced spine, or nested unfused product.
data RepObj (g :: Group) where
  I     :: RepObj g
  REP   :: Rep g -> RepObj g
  (:⊗:) :: RepObj g -> RepObj g -> RepObj g

-- | @m `IrrepOf` j@ ≡ multiplicity @m@ of irrep @j@ (flips @'(j, m)@).
type (m :: Nat) `IrrepOf` j = '(j, m)

-- | Image of the forgetful functor (group-indexed).
type family ToVector (g :: Group) (o :: RepObj g) :: Type where
  ToVector g 'I         = C 1
  ToVector g ('REP r)   = C (RepDimG g r)
  ToVector g (a ':⊗: b) = ToVector g a ⊗ ToVector g b
