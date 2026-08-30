{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

-- | Green-field symbolic SU(2) reps: sector keys are bare @Nat@ (@2j@) with flat
-- or product multiplicity (@'AtomM m@ / @'Prod ('AtomM m) ('AtomM n)@).
--
-- Fusion-tree association is temporal (@FuseExpr@ then tensor again), so
-- tensors are always leaf×leaf. 'Coalesce' merges same-irrep sectors by
-- adding evaluated multiplicities into an @'AtomM@. 'RepV' is the indexed
-- term-level spine; 'coalesce' / 'fuseExpr' fold it directly (no spine class).
--
-- __Merge layout (coalesced):__ same-irrep sectors combine by direct sum
-- along the copy axis via 'TensorNetwork.Categorical.mergeCopyAxis' (and
-- 'flattenCopyProd' when a @'Prod'@ leg must collapse to @'AtomM'@ first).
-- Output multiplicity is always @'AtomM (EvalMult μ1 + …)@.
--
-- __RepExpr / ToV:__ unfused and dual spaces live on 'RepExpr', not on
-- sector keys. @'RTensor ('RSum r) ('RSum q)@ has
-- @ToV = ToVSpine r ⊗ ToVSpine q@ ('rtensor') and reduces through 'FuseExpr' /
-- 'fuseExpr' on atom pairs; @'RDual ('RSum r)@ is @DualVector (ToVSpine r)@
-- ('rdual'), paired by 'cupUnfused' / 'cupRdual' (primal⊗dual; unfused closed
-- in 'ToV', including @'RSum Unit@), with morphism spaces as 'MorExpr' / 'rmor'.
-- Unfused composition: 'composeMor' (@unitor ∘ (cup ⊗ id) ∘ assoc ∘ (f ⊗ g)@;
-- assoc = monoidal α). Fused composition: 'composeMorFused' on 'MorExprFused'
-- (@unitor ∘ cup ∘ fmove ∘ (f ⊗ g)@; steps stubbed). Fused cups/caps:
-- 'cupFused' / 'capFused'.
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
