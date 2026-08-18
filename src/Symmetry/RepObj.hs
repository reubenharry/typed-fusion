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
  , SectorVec
  , RepToSectors
  , ToSectors
  , type IrrepOf
  , type Of
  ) where

import Data.Kind (Type)
import GHC.TypeLits (Nat)
import Math.LinearMap.Category (type (⊗))
import Numeric.LinearAlgebra.Static (C)
import Symmetry.Group (Group (..), IrrepDim, Irreps, Rep, RepDimG)

-- | Object of the rep category: unit, reduced spine, or nested unfused product.
data RepObj (g :: Group) where
  I     :: RepObj g
  REP   :: Rep g -> RepObj g
  (:⊗:) :: RepObj g -> RepObj g -> RepObj g

-- | @m `IrrepOf` j@ ≡ multiplicity @m@ of irrep @j@ (flips @'(j, m)@).
type (m :: Nat) `IrrepOf` j = '(j, m)
type (m :: Nat) `Of` j = '(j, m)

-- | Image of the forgetful functor (group-indexed).
type family ToVector (g :: Group) (o :: RepObj g) :: Type where
  ToVector g 'I         = C 1
  ToVector g ('REP r)   = C (RepDimG g r)
  ToVector g (a ':⊗: b) = ToVector g a ⊗ ToVector g b

-- | One isotypical summand: multiplicity ⊗ irrep.
-- Matches @fuseSU2Flat@ / @su2ExpandBlock@ (@kron(coeff, I_j)@, 2nd factor fastest).
type family SectorVec (g :: Group) (j :: Irreps g) (m :: Nat) :: Type where
  SectorVec g j m = C m ⊗ C (IrrepDim g j)

-- | Spine-level biproduct of 'SectorVec's. Case-split on @g@ so @Rep g@
-- reduces (non-injective). Last sector is not paired with @()@; @'[]@ unmatched.
type family RepToSectors (g :: Group) (r :: Rep g) :: Type where
  RepToSectors U1  '[ '(z, m)]     = SectorVec U1 z m
  RepToSectors U1  ('(z, m) ': rs) = (SectorVec U1 z m, RepToSectors U1 rs)
  RepToSectors SU2 '[ '(j, m)]     = SectorVec SU2 j m
  RepToSectors SU2 ('(j, m) ': rs) = (SectorVec SU2 j m, RepToSectors SU2 rs)

-- | Direct-sum-preserving forgetful image (sibling of 'ToVector').
type family ToSectors (g :: Group) (o :: RepObj g) :: Type where
  ToSectors g 'I         = C 1
  ToSectors g (a ':⊗: b) = ToSectors g a ⊗ ToSectors g b
  ToSectors U1 ('REP r)  = RepToSectors U1 r
  ToSectors SU2 ('REP r) = RepToSectors SU2 r
