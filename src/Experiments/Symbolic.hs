{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

-- | Symbolic SU(2): skeletal 'HomFused' objects and genealogy 'Rep' morphisms.
--
-- Layers: 'Experiments.Fusion.Obj.Obj' → 'HomUnfused' / 'ToVObj'; skeletal
-- 'Spine' → 'HomFused' / 'HomInter' with 'RepV' / 'FuseRep' morphisms /
-- 'composeHomTrees' (HomInter: embed → compose → filter).
--
-- Hierarchy: 'Experiments.Symbolic.Expr' (kinds),
-- 'Experiments.Symbolic.TypeLevel' (families),
-- 'Experiments.Symbolic.Singletons' / 'RepV' / 'FMove' / 'Core' (term-level),
-- 'Experiments.Symbolic.Smoke' (concrete spines + checks).
-- Examples: 'Experiments.SymbolicExamples'.
module Experiments.Symbolic
  ( module Experiments.Symbolic.Expr
  , module Experiments.Symbolic.TypeLevel
  , module Experiments.Symbolic.Aliases
  , module Experiments.Symbolic.Singletons
  , module Experiments.Symbolic.RepV
  , module Experiments.Symbolic.FMove
  , module Experiments.Symbolic.Core
  , module Experiments.Symbolic.Smoke
  ) where

import Experiments.Symbolic.Aliases
import Experiments.Symbolic.Core
import Experiments.Symbolic.Expr
import Experiments.Symbolic.FMove
import Experiments.Symbolic.RepV
import Experiments.Symbolic.Singletons
import Experiments.Symbolic.Smoke
import Experiments.Symbolic.TypeLevel
