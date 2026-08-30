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

-- | Symbolic SU(2) irrep / multiplicity expression kinds.
--
-- 'RepExpr' is the @ToV@ / space layer (unfused Kronecker, duals, Hom packing).
-- Categorical objects for the symbolic monoidal category are
-- 'Experiments.Fusion.Obj.Obj' trees (@'Atom@ \/ @'Tensor@ \/ @'Sum@); nested
-- Mac Lane parenthesization lives there, not on 'RepExpr'.
-- Sector keys are bare @Nat@ (@2j@); multiplicity stays a small expression kind.
module Experiments.Symbolic.Expr
  ( MultExpr (..)
  , Sector
  , Rep
  , RepExpr (..)
  ) where

import GHC.TypeLits (Nat)

-- | Formal multiplicity: leaf @m@ or an unfused product of copy spaces.
data MultExpr
  = AtomM Nat
  | Prod MultExpr MultExpr

-- | Sector: irrep label (@2j@ as 'Nat') paired with a multiplicity expression.
type Sector = (Nat, MultExpr)
type Rep = [Sector]

-- | Expression over coalesced spines: direct sum, unfused tensor, or dual.
--
-- This is /not/ the categorical object kind (see @Obj@ in
-- 'Experiments.Fusion.Obj'). Well-formed @'RTensor@: both arguments are atom
-- @'RSum@ spines (no nested @'RTensor@). Deeper association is temporal
-- (@FuseExpr@ then @'RTensor@ again) or formal on @Obj@ trees via 'FuseSym'.
data RepExpr
  = RSum Rep
  | RTensor RepExpr RepExpr
  | RDual RepExpr
