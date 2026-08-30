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
module Experiments.Symbolic.Expr
  ( MultExpr (..)
  , Sector
  , Rep
  ) where

import GHC.TypeLits (Nat)

-- | Formal multiplicity: leaf @m@ or an unfused product of copy spaces.
data MultExpr
  = AtomM Nat
  | Prod MultExpr MultExpr

-- | Sector: irrep label (@2j@ as 'Nat') paired with a multiplicity expression.
type Sector = (Nat, MultExpr)
type Rep = [Sector]
