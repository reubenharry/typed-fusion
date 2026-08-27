{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

-- | Green-field symbolic SU(2) reps: flat irrep @'Tensor ('Atom j1) ('Atom j2)@ and flat
-- multiplicity @'Prod ('AtomM m) ('AtomM n)@.
--
-- Fusion-tree association is temporal (@Fuse@ then tensor again), so tensors
-- are always leaf×leaf. 'Coalesce' merges same-'IrrepExpr' sectors by adding
-- evaluated multiplicities into an @'AtomM@. 'RepV' is the indexed term-level
-- spine; 'fuseRaw' / 'coalesce' fold it directly (no spine class).
--
-- __Merge layout (coalesced):__ same-'IrrepExpr' sectors combine by direct sum
-- along the copy axis via 'TensorNetwork.Categorical.mergeCopyAxis' (and
-- 'flattenCopyProd' / 'flattenTensorProdCopy' when a @'Prod'@ leg must
-- collapse to @'AtomM'@ first). Output multiplicity is always
-- @'AtomM (EvalMult μ1 + …)@.
--
-- Tensor CG fuse uses typed 'Symmetry.CG.SU2.fuseCGChannel' per channel; see
-- 'Experiments.Symbolic.Reference' for flat-buffer oracles.
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
