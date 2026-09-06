{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

-- | Symbolic SU(2): genealogy 'Rep' trees and unfused 'Obj' Hom.
--
-- Layers: 'Experiments.Fusion.Obj.Obj' → 'HomUnfused' / 'ToVObj'; fusion-tree
-- 'Rep' / 'RepV' → 'HomFused' / 'fuseRepTerm' / 'composeHomTrees'.
--
-- Hierarchy: 'Experiments.Symbolic.Expr' (kinds),
-- 'Experiments.Symbolic.TypeLevel' (families), 'Experiments.Symbolic.Core'
-- (term-level). Examples: 'Experiments.SymbolicExamples'.
module Experiments.Symbolic
  ( module Experiments.Symbolic.Expr
  , module Experiments.Symbolic.TypeLevel
  , module Experiments.Symbolic.Core
  ) where

import Experiments.Symbolic.Core
import Experiments.Symbolic.Expr
import Experiments.Symbolic.TypeLevel
