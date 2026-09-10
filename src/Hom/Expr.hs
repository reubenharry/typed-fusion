{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

-- | Symbolic fusion-tree kinds (label-polymorphic).
--
-- Unfused Hom indexes 'Fusion.Obj.Obj' trees. Fused Hom indexes
-- the same 'Obj' trees (via 'ObjFTrees' / 'TheoryOf'); morphisms are
-- genealogy-preserving fusion trees ('FTree' \/ 'FTrees' / 'FuseFTrees').
-- SU(2) uses @lab ~ Nat@ (@2j@); U(1) uses @lab ~ Z@.
module Hom.Expr
  ( FTree (..)
  , FTrees
  ) where

-- | Fusion tree: one inhabited channel plus genealogy.
--
-- @'IrrepTree j@ is a bare label. @j `'From` '(l, r)@ is the CG outcome @j@
-- of coupling children @l@ and @r@ (multiplicity-free; no channel index).
--
-- Children are paired so @From@ can be infix (Haskell infix constructors are
-- binary).
data FTree lab
  = IrrepTree lab
  | lab `From` (FTree lab, FTree lab)

-- | List of fusion trees (same-root trees stay distinct).
type FTrees lab = [FTree lab]
