{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

-- | Green-field symbolic SU(2) reps: sector keys are bare @Nat@ (@2j@) with flat
-- or product multiplicity (@'AtomM m@ / @'Prod ('AtomM m) ('AtomM n)@).
--
-- Categorical objects are 'Experiments.Fusion.Obj.Obj' trees; 'FuseSym' forgets
-- to a coalesced 'Rep' spine (@FuseRep@ with unitors). Hom \/ cup packing is
-- Dual-left @Dual(ToVSpine ·) ⊗ ToVSpine ·@ over spines (no parallel expression AST).
--
-- 'Coalesce' merges same-irrep sectors by adding evaluated multiplicities into
-- an @'AtomM@. 'RepV' is the indexed term-level spine; 'coalesce' / 'fuseExpr'
-- fold it directly.
--
-- Unfused composition: 'composeMorObj' \/ 'HomUnfused' on @ToVObj@ trees
-- (complete Category; linearmap α / unitors). Fused Hom: 'HomFused' as
-- @ToVSpine (FuseHom (FuseSym ·) (FuseSym ·))@ (Category @(. )@ stubbed).
-- Fused cups/caps: 'cupFused' / 'capFused' on @FilterTrivial (FuseHom r r)@.
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
