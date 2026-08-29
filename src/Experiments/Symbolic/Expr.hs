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
module Experiments.Symbolic.Expr
  ( IrrepExpr (..)
  , MultExpr (..)
  , Sector
  , Rep
  , RepExpr (..)
  ) where

import GHC.TypeLits (Nat)

-- | SU(2) irrep label: a single leaf @j@.
--
-- Unfused tensor and dual spaces live on 'RepExpr' (@'RTensor@ / @'RDual@), so
-- a 'Sector' key is always an atom and sector payloads never carry a formal
-- tensor / dual constructor.
data IrrepExpr = Atom Nat

-- | Formal multiplicity: leaf @m@ or an unfused product of copy spaces.
data MultExpr
  = AtomM Nat
  | Prod MultExpr MultExpr

type Sector = (IrrepExpr, MultExpr)
type Rep = [Sector]

-- | Expression over coalesced spines: direct sum, unfused tensor, or dual.
--
-- Well-formed @'RTensor@: both arguments are atom @'RSum@ spines (no nested
-- @'RTensor@). Deeper association is temporal (@FuseExpr@ then @'RTensor@ again).
data RepExpr
  = RSum Rep
  | RTensor RepExpr RepExpr
  | RDual RepExpr
