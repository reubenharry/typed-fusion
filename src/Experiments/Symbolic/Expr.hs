{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Symbolic SU(2) multiplicity / sector kinds.
--
-- Categorical objects are 'Experiments.Fusion.Obj.Obj' trees. Sector spines are
-- coalesced @Rep = [(Nat, MultExpr)]@ (@2j@ keys). Hom packing lives in
-- 'Experiments.Symbolic.TypeLevel' (Dual-left over 'ToVSpine' \/ 'ToVObj').
--
-- 'Irrep' fusion trees track genealogy (how a channel was coupled); 'TreeRep'
-- is a list of such trees. Coalesced 'Rep' remains the flat sector / Reference
-- spine; fused Hom packing is on trees.
module Experiments.Symbolic.Expr
  ( MultExpr (..)
  , Sector
  , Rep
  , Irrep (..)
  , TreeRep
  ) where

import GHC.TypeLits (Nat)

-- | Formal multiplicity: leaf @m@ or an unfused product of copy spaces.
data MultExpr
  = AtomM Nat
  | Prod MultExpr MultExpr

-- | Sector: irrep label (@2j@ as 'Nat') paired with a multiplicity expression.
type Sector = (Nat, MultExpr)
type Rep = [Sector]

-- | Fusion tree: one inhabited SU(2) channel plus genealogy.
--
-- @'Leaf j@ is a bare @2j@ label. @'Node j l r@ is the CG outcome @j@ of
-- coupling children @l@ and @r@ (SU(2) multiplicity-free; no channel index).
data Irrep
  = Leaf Nat
  | Node Nat Irrep Irrep

-- | Representation as a list of fusion trees (parallel to coalesced 'Rep').
type TreeRep = [Irrep]
