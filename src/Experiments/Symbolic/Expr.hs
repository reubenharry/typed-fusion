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
  ) where

import GHC.TypeLits (Nat)

-- | SU(2) irrep expression: leaf @j@, unfused tensor, or dual.
--
-- @'Tensor@ is recursive so @'Atom@ ⊗ @'Dual ('Atom …)@ is expressible.
-- Historical leaf pairs @'Tensor ('Atom j1) ('Atom j2)@ become @'Tensor ('Atom j1) ('Atom j2)@.
data IrrepExpr
  = Atom Nat
  | Tensor IrrepExpr IrrepExpr
  | Dual IrrepExpr

-- | Formal multiplicity: leaf @m@, unfused product, or dual.
-- Historical @'Prod ('AtomM m) ('AtomM n)@ becomes @'Prod ('AtomM m) ('AtomM n)@.
data MultExpr
  = AtomM Nat
  | Prod MultExpr MultExpr
  | DualM MultExpr

type Sector = (IrrepExpr, MultExpr)
type Rep = [Sector]
