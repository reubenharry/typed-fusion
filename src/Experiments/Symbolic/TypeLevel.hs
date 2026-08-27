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

-- | Type-level braid, dual, coalesce, fuse, and tensor for symbolic reps.
module Experiments.Symbolic.TypeLevel
  ( -- * Braid
    BraidIrrep
  , BraidMult
  , BraidSector
  , Braid
    -- * Dual / unit / morphisms
  , DualIrrep
  , DualMult
  , DualSector
  , Dual
  , Unit
  , Mor
    -- * Multiplicity
  , EvalMult
  , AddMult
    -- * Coalesce (sorted merge)
  , CmpIrrep
  , CmpIrrepTensor2
  , InsertSector
  , InsertSectorOrd
  , Coalesce
  , FilterTrivial
    -- * Sector spaces
  , IrrepDim
  , ToVSector
    -- * Fusion / tensor
  , UndualIrrep
  , UndualMult
  , AtomsFromCG
  , FuseIrrepPrimal
  , FuseIrrep
  , TagMult
  , FuseSector
  , FuseRepRaw
  , Fuse
  , TensorPair
  , TensorOne
  , Tensor
    -- * Spine constraints
  , AtomSpine
  , DualAtomSpine
  ) where

import Data.Kind (Constraint, Type)
import Experiments.SU2 (TensorIrrepRepSU2)
import Experiments.Symbolic.Expr
import GHC.TypeLits (CmpNat, KnownNat, Nat, type (*), type (+))
import Math.LinearMap.Category (DualVector, type (⊗))
import Numeric.LinearAlgebra.Static (C)
import Symmetry.Utils (Append)

-- Braid (swap tensor factors on each sector)
--------------------------------------------------------------------------------

-- | Swap irrep / copy factors sector-wise.
type family BraidIrrep (e :: IrrepExpr) :: IrrepExpr where
  BraidIrrep ('Atom j) = 'Atom j
  BraidIrrep ('Tensor e1 e2) = 'Tensor (BraidIrrep e2) (BraidIrrep e1)
  BraidIrrep ('Dual e) = 'Dual (BraidIrrep e)

type family BraidMult (μ :: MultExpr) :: MultExpr where
  BraidMult ('AtomM m) = 'AtomM m
  BraidMult ('Prod μ1 μ2) = 'Prod (BraidMult μ2) (BraidMult μ1)
  BraidMult ('DualM μ) = 'DualM (BraidMult μ)

type family BraidSector (s :: Sector) :: Sector where
  BraidSector '(e, μ) = '(BraidIrrep e, BraidMult μ)

-- | Braid every sector in a spine (@Braid (Tensor r s)@ swaps each distributed pair).
type family Braid (rs :: Rep) :: Rep where
  Braid '[] = '[]
  Braid (s ': rs) = BraidSector s ': Braid rs

--------------------------------------------------------------------------------
-- Dual (compact closed)
--
-- Unfused duals are real @'Dual@ / @'DualM@ on leaves; 'DualIrrep' / 'DualMult'
-- distribute over @'Tensor@ / @'Prod@ (reverse factors) so dual is involutive.
-- 'ToVSector' on a dual leaf is 'DualVector'; on a dualized tensor it becomes
-- @DualVector ⊗ DualVector@ via the recursive tensor rule (≅ linearmap
-- @DualVector (u ⊗ v)@). SU(2) CS / U(1) charge-flip into ordinary @'Atom@
-- spines is a later Fuse (or undual) step — not a silent type equality.
--------------------------------------------------------------------------------

-- | Dual of an irrep expression (involutive; reverses tensor factors).
type family DualIrrep (e :: IrrepExpr) :: IrrepExpr where
  DualIrrep ('Dual e) = e
  DualIrrep ('Atom j) = 'Dual ('Atom j)
  DualIrrep ('Tensor e1 e2) = 'Tensor (DualIrrep e2) (DualIrrep e1)

-- | Dual of a multiplicity expression (involutive; reverses products).
type family DualMult (μ :: MultExpr) :: MultExpr where
  DualMult ('DualM μ) = μ
  DualMult ('AtomM m) = 'DualM ('AtomM m)
  DualMult ('Prod μ1 μ2) = 'Prod (DualMult μ2) (DualMult μ1)

-- | Dual of one sector: dualize irrep and multiplicity together.
type family DualSector (s :: Sector) :: Sector where
  DualSector '(e, μ) = '(DualIrrep e, DualMult μ)

-- | Dual of a spine (sector-wise).
type family Dual (rs :: Rep) :: Rep where
  Dual '[] = '[]
  Dual (s ': rs) = DualSector s ': Dual rs

-- | Monoidal unit: trivial irrep @j = 0@ with unit multiplicity.
type Unit = '[ '( 'Atom 0, 'AtomM 1)]

-- | Morphisms @r → q@ as elements of @Dual r ⊗ q@ (unfused leaf×leaf distribute).
type Mor (r :: Rep) (q :: Rep) = Tensor (Dual r) q

--------------------------------------------------------------------------------
-- Multiplicity evaluation / merge
--------------------------------------------------------------------------------

-- | Dimension of a multiplicity expression.
type family EvalMult (μ :: MultExpr) :: Nat where
  EvalMult ('AtomM m) = m
  EvalMult ('Prod μ1 μ2) = EvalMult μ1 * EvalMult μ2
  EvalMult ('DualM μ) = EvalMult μ

-- | Same-key merge: always an @'AtomM@ of summed dimensions.
type family AddMult (μ1 :: MultExpr) (μ2 :: MultExpr) :: MultExpr where
  AddMult μ1 μ2 = 'AtomM (EvalMult μ1 + EvalMult μ2)

--------------------------------------------------------------------------------
-- Coalesce: sort + merge sectors with equal 'IrrepExpr'
--------------------------------------------------------------------------------

-- | Total order: @'Atom@ < @'Tensor@ < @'Dual@; then structural.
type family CmpIrrep (a :: IrrepExpr) (b :: IrrepExpr) :: Ordering where
  CmpIrrep ('Atom j) ('Atom k) = CmpNat j k
  CmpIrrep ('Atom _) ('Tensor _ _) = 'LT
  CmpIrrep ('Atom _) ('Dual _) = 'LT
  CmpIrrep ('Tensor _ _) ('Atom _) = 'GT
  CmpIrrep ('Dual _) ('Atom _) = 'GT
  CmpIrrep ('Tensor _ _) ('Dual _) = 'LT
  CmpIrrep ('Dual _) ('Tensor _ _) = 'GT
  CmpIrrep ('Tensor e1 e2) ('Tensor f1 f2) =
    CmpIrrepTensor2 (CmpIrrep e1 f1) e2 f2
  CmpIrrep ('Dual e) ('Dual f) = CmpIrrep e f

type family CmpIrrepTensor2
  (o :: Ordering) (e2 :: IrrepExpr) (f2 :: IrrepExpr) :: Ordering where
  CmpIrrepTensor2 'EQ e2 f2 = CmpIrrep e2 f2
  CmpIrrepTensor2 o _ _ = o

-- | Insert one sector into an already-coalesced (sorted, merged) spine.
type family InsertSector (e :: IrrepExpr) (μ :: MultExpr) (rs :: Rep) :: Rep where
  InsertSector e μ '[] = '[ '(e, μ)]
  InsertSector e μ ('(e2, μ2) ': rest) =
    InsertSectorOrd (CmpIrrep e e2) e μ e2 μ2 rest

type family InsertSectorOrd
  (o :: Ordering)
  (e :: IrrepExpr) (μ :: MultExpr)
  (e2 :: IrrepExpr) (μ2 :: MultExpr)
  (rest :: Rep)
  :: Rep
 where
  InsertSectorOrd 'EQ e μ _ μ2 rest = '(e, AddMult μ μ2) ': rest
  InsertSectorOrd 'LT e μ e2 μ2 rest = '(e, μ) ': '(e2, μ2) ': rest
  InsertSectorOrd 'GT e μ e2 μ2 rest = '(e2, μ2) ': InsertSector e μ rest

-- | Fold @InsertSector@ over a raw spine → sorted, merged 'Rep'.
type family Coalesce (rs :: Rep) :: Rep where
  Coalesce '[] = '[]
  Coalesce ('(e, μ) ': rest) = InsertSector e μ (Coalesce rest)

-- | Keep only the SU(2) trivial irrep (@'Atom 0@); drop everything else.
-- Typical use: after 'Fuse' \/ 'Coalesce', project to singlets (Hom space).
type family FilterTrivial (rs :: Rep) :: Rep where
  FilterTrivial '[] = '[]
  FilterTrivial ('( 'Atom 0, μ) ': rest) =
    '( 'Atom 0, μ) ': FilterTrivial rest
  FilterTrivial ('(e, μ) ': rest) = FilterTrivial rest

--------------------------------------------------------------------------------
-- Sector spaces (concrete vectors indexed by irrep / multiplicity)
--------------------------------------------------------------------------------

-- | SU(2) irrep dimension @j ↦ j + 1@.
type family IrrepDim (j :: Nat) :: Nat where
  IrrepDim j = j + 1

-- | Sector space from irrep expression + multiplicity.
--
-- Dual sectors are linearmap 'DualVector's of the undualized sector (factorwise
-- @DualVector u ⊗ DualVector v@ is isomorphic to @DualVector (u ⊗ v)@).
type family ToVSector (e :: IrrepExpr) (μ :: MultExpr) :: Type where
  ToVSector ('Atom j) ('AtomM m) = C m ⊗ C (IrrepDim j)
  ToVSector ('Atom j) ('Prod ('AtomM m) ('AtomM n)) =
    (C m ⊗ C n) ⊗ C (IrrepDim j)
  ToVSector ('Tensor ('Atom j1) ('Atom j2)) ('AtomM m) =
    C m ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2)
  ToVSector ('Tensor ('Atom j1) ('Atom j2)) ('Prod ('AtomM m) ('AtomM n)) =
    (C m ⊗ C (IrrepDim j1)) ⊗ (C n ⊗ C (IrrepDim j2))
  -- Recursive unfused tensor: payload is the tensor of the two leaf sectors.
  ToVSector ('Tensor e1 e2) ('Prod μ1 μ2) =
    ToVSector e1 μ1 ⊗ ToVSector e2 μ2
  -- Matched dual: DualVector of the primal sector space.
  ToVSector ('Dual e) ('DualM μ) = DualVector (ToVSector e μ)

--------------------------------------------------------------------------------
-- Fusion: CG on irreps, then coalesced rep
--------------------------------------------------------------------------------

-- | Strip @'Dual@ wrappers: SU(2) @'Dual ('Atom j)@ identifies with @'Atom j@.
-- (U(1) charge flip would negate labels here when that lands.)
type family UndualIrrep (e :: IrrepExpr) :: IrrepExpr where
  UndualIrrep ('Atom j) = 'Atom j
  UndualIrrep ('Dual e) = UndualIrrep e
  UndualIrrep ('Tensor e1 e2) = 'Tensor (UndualIrrep e1) (UndualIrrep e2)

-- | Strip @'DualM@ wrappers so fused spines carry ordinary @'AtomM@ / @'Prod@.
type family UndualMult (μ :: MultExpr) :: MultExpr where
  UndualMult ('AtomM m) = 'AtomM m
  UndualMult ('DualM μ) = UndualMult μ
  UndualMult ('Prod μ1 μ2) = 'Prod (UndualMult μ1) (UndualMult μ2)

-- | Tag every CG channel with unit multiplicity (irrep-only fuse).
type family AtomsFromCG (cg :: [(Nat, Nat)]) :: Rep where
  AtomsFromCG '[] = '[]
  AtomsFromCG ('(j, _) ': rest) = '( 'Atom j, 'AtomM 1) ': AtomsFromCG rest

-- | CG-fuse a primal (undualed) irrep expression.
type family FuseIrrepPrimal (e :: IrrepExpr) :: Rep where
  FuseIrrepPrimal ('Atom j) = '[ '( 'Atom j, 'AtomM 1)]
  FuseIrrepPrimal ('Tensor ('Atom j1) ('Atom j2)) =
    AtomsFromCG (TensorIrrepRepSU2 j1 j2)

-- | Fuse one 'IrrepExpr': undual Dual labels, then CG on primal atoms.
type family FuseIrrep (e :: IrrepExpr) :: Rep where
  FuseIrrep e = FuseIrrepPrimal (UndualIrrep e)

-- | Attach a sector multiplicity to every atom in a fused irrep spine.
type family TagMult (μ :: MultExpr) (rs :: Rep) :: Rep where
  TagMult μ '[] = '[]
  TagMult μ ('( 'Atom j, _) ': rest) = '( 'Atom j, μ) ': TagMult μ rest

-- | Fuse one sector: undual multiplicity, CG the (undualed) irrep, tag copies.
type family FuseSector (s :: Sector) :: Rep where
  FuseSector '(e, μ) = TagMult (UndualMult μ) (FuseIrrep e)

-- | Fuse every sector in a spine, append, then coalesce.
type family FuseRepRaw (rs :: Rep) :: Rep where
  FuseRepRaw '[] = '[]
  FuseRepRaw (s ': rest) = Append (FuseSector s) (FuseRepRaw rest)

-- | Full fusion of a 'Rep': all @'Tensor'@ edges CG-reduced, same keys merged.
type family Fuse (rs :: Rep) :: Rep where
  Fuse rs = Coalesce (FuseRepRaw rs)

-- | Distribute: tensor product of two leaf sectors (primal or dual).
type family TensorPair (s1 :: Sector) (s2 :: Sector) :: Sector where
  TensorPair '(e1, μ1) '(e2, μ2) = '( 'Tensor e1 e2, 'Prod μ1 μ2)

type family TensorOne (s :: Sector) (q :: Rep) :: Rep where
  TensorOne _ '[] = '[]
  TensorOne s (s2 ': rest) =
    Append '[TensorPair s s2] (TensorOne s rest)

type family Tensor (r :: Rep) (q :: Rep) :: Rep where
  Tensor '[] _ = '[]
  Tensor (s ': rs) q = Append (TensorOne s q) (Tensor rs q)

--------------------------------------------------------------------------------
-- Spine singletons
--
-- One general 'SRep' (plus 'SIrrep' / 'SMult'). Narrow proofs 'KnownAtomRep' /
-- 'KnownDualAtomRep' refine which spines are inhabited; walks use 'symRepSing'.
--------------------------------------------------------------------------------

-- | Constraint: spine is leaf atoms with @'AtomM@ multiplicities (tensor domain).
type family AtomSpine (rs :: Rep) :: Constraint where
  AtomSpine '[] = ()
  AtomSpine ('( 'Atom j, 'AtomM m) ': rest) =
    ( KnownNat j
    , KnownNat m
    , KnownNat (IrrepDim j)
    , AtomSpine rest
    )

-- | Constraint: spine is dual-atom leaves (@'Dual ('Atom j)@ / @'DualM ('AtomM m)@).
type family DualAtomSpine (rs :: Rep) :: Constraint where
  DualAtomSpine '[] = ()
  DualAtomSpine ('( 'Dual ('Atom j), 'DualM ('AtomM m)) ': rest) =
    ( KnownNat j
    , KnownNat m
    , KnownNat (IrrepDim j)
    , DualAtomSpine rest
    )
