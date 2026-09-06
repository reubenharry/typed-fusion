{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

-- | Symbolic SU(2) fusion-tree kinds.
--
-- Categorical objects are 'Experiments.Fusion.Obj.Obj' trees (@'Atom@ \/
-- @'Tensor@ \/ @'Sum@). Representations are genealogy-preserving fusion trees
-- ('Irrep' \/ 'Rep'). There is no coalesced sector spine — flat buffers live
-- only in oracles if reintroduced later.
module Experiments.Symbolic.Expr
  ( Irrep (..)
  , Rep
  ) where

import GHC.TypeLits (Nat)

-- | Fusion tree: one inhabited SU(2) channel plus genealogy.
--
-- @'Leaf j@ is a bare @2j@ label. @'Node j l r@ is the CG outcome @j@ of
-- coupling children @l@ and @r@ (SU(2) multiplicity-free; no channel index).
data Irrep
  = Leaf Nat
  | Node Nat Irrep Irrep

-- | Representation as a list of fusion trees (same-root trees stay distinct).
type Rep = [Irrep]
