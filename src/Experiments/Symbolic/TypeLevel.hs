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

-- | Type-level braid, coalesce, and fuse for symbolic atom reps.
--
-- Sectors are atom-keyed ('IrrepExpr' has only @'Atom@), so unfused tensor and
-- dual spaces are expressed on 'RepExpr' (@'RTensor@ / @'RDual@) and reduced by
-- 'FuseExpr' / 'ToV' rather than by formal @'Tensor@ / @'Dual@ irreps.
module Experiments.Symbolic.TypeLevel
  ( -- * Braid
    BraidIrrep
  , BraidMult
  , BraidSector
  , Braid
    -- * Unit
  , Unit
    -- * Multiplicity
  , EvalMult
  , AddMult
    -- * Coalesce (sorted merge)
  , CmpIrrep
  , InsertSector
  , InsertSectorOrd
  , Coalesce
  , FilterTrivial
    -- * Sector spaces
  , IrrepDim
  , ToVSector
  , ToVSpine
  , ToV
  , BraidExpr
  , FuseExpr
  , FuseAtoms
  , FuseAtomSpineOne
  , FuseAtomSpines
  , DualExpr
  , MorExpr
  , CupUnfusedExpr
  , CapUnfusedExpr
  , CupFusedRep
  , CapFusedRep
  , ComposeTensorExpr
  , ComposeAssocExpr
  , ComposeCuppedExpr
    -- * Fusion
  , AtomsFromCG
  , FuseIrrep
  , TagMult
  , FuseSector
  , FuseRepRaw
  , Fuse
    -- * Spine constraints
  , AtomSpine
  ) where

import Data.Kind (Constraint, Type)
import Experiments.SU2 (TensorIrrepRepSU2)
import Experiments.Symbolic.Expr
import GHC.TypeLits (CmpNat, KnownNat, Nat, type (*), type (+))
import Math.LinearMap.Category (DualVector, type (⊗))
import Numeric.LinearAlgebra.Static (C)
import Symmetry.Utils (Append)

-- Braid (swap copy factors on each sector)
--------------------------------------------------------------------------------

-- | Irrep keys are atoms, so braiding leaves them fixed.
type family BraidIrrep (e :: IrrepExpr) :: IrrepExpr where
  BraidIrrep ('Atom j) = 'Atom j

type family BraidMult (μ :: MultExpr) :: MultExpr where
  BraidMult ('AtomM m) = 'AtomM m
  BraidMult ('Prod μ1 μ2) = 'Prod (BraidMult μ2) (BraidMult μ1)

type family BraidSector (s :: Sector) :: Sector where
  BraidSector '(e, μ) = '(BraidIrrep e, BraidMult μ)

-- | Braid every sector in a spine (swap the @'Prod@ copy factors).
type family Braid (rs :: Rep) :: Rep where
  Braid '[] = '[]
  Braid (s ': rs) = BraidSector s ': Braid rs

-- | Monoidal unit: trivial irrep @j = 0@ with unit multiplicity.
type Unit = '[ '( 'Atom 0, 'AtomM 1)]

--------------------------------------------------------------------------------
-- Multiplicity evaluation / merge
--------------------------------------------------------------------------------

-- | Dimension of a multiplicity expression.
type family EvalMult (μ :: MultExpr) :: Nat where
  EvalMult ('AtomM m) = m
  EvalMult ('Prod μ1 μ2) = EvalMult μ1 * EvalMult μ2

-- | Same-key merge: always an @'AtomM@ of summed dimensions.
type family AddMult (μ1 :: MultExpr) (μ2 :: MultExpr) :: MultExpr where
  AddMult μ1 μ2 = 'AtomM (EvalMult μ1 + EvalMult μ2)

--------------------------------------------------------------------------------
-- Coalesce: sort + merge sectors with equal 'IrrepExpr'
--------------------------------------------------------------------------------

-- | Total order on atom keys.
type family CmpIrrep (a :: IrrepExpr) (b :: IrrepExpr) :: Ordering where
  CmpIrrep ('Atom j) ('Atom k) = CmpNat j k

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

-- | Sector space from irrep label + multiplicity.
type family ToVSector (e :: IrrepExpr) (μ :: MultExpr) :: Type where
  ToVSector ('Atom j) ('AtomM m) = C m ⊗ C (IrrepDim j)
  ToVSector ('Atom j) ('Prod ('AtomM m) ('AtomM n)) =
    (C m ⊗ C n) ⊗ C (IrrepDim j)

-- | Forgetful direct-sum space of a spine: right-nested sector payloads.
--
-- Singleton @'[s]@ is just @ToVSector s@; longer spines are
-- @(ToVSector s1, ToVSpine rest)@ (no @()@ terminator — that breaks
-- linearmap @Scalar@ / @⊗@). Empty spine is unsupported as an @LSpace@.
type family ToVSpine (rs :: Rep) :: Type where
  ToVSpine '[ '(e, μ) ] = ToVSector e μ
  ToVSpine ('(e, μ) ': s ': rest) =
    (ToVSector e μ, ToVSpine (s ': rest))

-- | Space of a 'RepExpr': nested-tuple @⊕@ for sums, @⊗@ for unfused tensors.
type family ToV (e :: RepExpr) :: Type where
  ToV ('RSum rs) = ToVSpine rs
  ToV ('RTensor a b) = ToV a ⊗ ToV b
  ToV ('RDual a) = DualVector (ToV a)

-- | Braid a 'RepExpr': swap @'RTensor@ factors.
type family BraidExpr (e :: RepExpr) :: RepExpr where
  BraidExpr ('RSum rs) = 'RSum (Braid rs)
  BraidExpr ('RTensor a b) = 'RTensor b a

-- | Dual of a 'RepExpr' (whole-expression dual).
type family DualExpr (e :: RepExpr) :: RepExpr where
  DualExpr e = 'RDual e

-- | Morphisms @r → q@ as @'RTensor ('RDual ('RSum r)) ('RSum q)@.
type MorExpr (r :: Rep) (q :: Rep) =
  'RTensor ('RDual ('RSum r)) ('RSum q)

-- Compact closed cups / caps (primal⊗dual for eval/coev; 'MorExpr' stays Dual-left)
--
-- Unfused: closed in 'ToV' (@RepExpr@ spaces, including @'RSum Unit@).
-- Fused: 'RepV' on singlet spines after dual≅primal and 'FuseExpr'.
-- Cap on ⊕ is the diagonal coevaluation (biproduct natural η).
--
-- Unfused object: @r ⊗ r*@ ('CupUnfusedExpr' / primal⊗dual).
--------------------------------------------------------------------------------

-- | Unfused cup/cap object: @r ⊗ r*@ as a 'RepExpr'.
type CupUnfusedExpr (r :: Rep) =
  'RTensor ('RSum r) ('RDual ('RSum r))

-- | Same object as 'CupUnfusedExpr' (η and ε are opposite maps on it).
type CapUnfusedExpr (r :: Rep) = CupUnfusedExpr r

-- | Fused cup domain: trivial channels of @FuseExpr (r ⊗ r)@ (after dual≅primal).
type CupFusedRep (r :: Rep) =
  FilterTrivial (FuseExpr ('RTensor ('RSum r) ('RSum r)))

-- | Fused cap codomain: same singlet spine as 'CupFusedRep'.
type CapFusedRep (r :: Rep) = CupFusedRep r

--------------------------------------------------------------------------------
-- Unfused composition stages (@compose = unitor ∘ (cup ⊗ id) ∘ assoc ∘ (f ⊗ g)@)
--
-- Hom packing is Dual-left ('MorExpr'). Cup on the middle uses primal⊗dual
-- ('CupUnfusedExpr'); 'assocCompose' is monoidal @α@ (rassoc then id⊗lassoc).
--------------------------------------------------------------------------------

-- | Step 1: @f ⊗ g@ with @f ∈ Mor a b@, @g ∈ Mor b c@.
type ComposeTensorExpr (a :: Rep) (b :: Rep) (c :: Rep) =
  'RTensor (MorExpr a b) (MorExpr b c)

-- | Step 2: @Dual a ⊗ ((b ⊗ Dual b) ⊗ c)@ — middle ready for 'cupUnfused'.
type ComposeAssocExpr (a :: Rep) (b :: Rep) (c :: Rep) =
  'RTensor
    ('RDual ('RSum a))
    ('RTensor (CupUnfusedExpr b) ('RSum c))

-- | Step 3: @Dual a ⊗ (Unit ⊗ c)@ after @(cup ⊗ id)@ on the middle.
type ComposeCuppedExpr (a :: Rep) (b :: Rep) (c :: Rep) =
  'RTensor
    ('RDual ('RSum a))
    ('RTensor ('RSum Unit) ('RSum c))

--------------------------------------------------------------------------------
-- Fusion: CG on atom pairs, then coalesced rep
--------------------------------------------------------------------------------

-- | Tag every CG channel with unit multiplicity (irrep-only fuse).
type family AtomsFromCG (cg :: [(Nat, Nat)]) :: Rep where
  AtomsFromCG '[] = '[]
  AtomsFromCG ('(j, _) ': rest) = '( 'Atom j, 'AtomM 1) ': AtomsFromCG rest

-- | Fuse one 'IrrepExpr': atoms are already fused.
type family FuseIrrep (e :: IrrepExpr) :: Rep where
  FuseIrrep ('Atom j) = '[ '( 'Atom j, 'AtomM 1)]

-- | Attach a sector multiplicity to every atom in a fused irrep spine.
type family TagMult (μ :: MultExpr) (rs :: Rep) :: Rep where
  TagMult μ '[] = '[]
  TagMult μ ('( 'Atom j, _) ': rest) = '( 'Atom j, μ) ': TagMult μ rest

-- | Fuse one sector: CG the irrep, tag copies.
type family FuseSector (s :: Sector) :: Rep where
  FuseSector '(e, μ) = TagMult μ (FuseIrrep e)

-- | Fuse every sector in a spine, append, then coalesce.
type family FuseRepRaw (rs :: Rep) :: Rep where
  FuseRepRaw '[] = '[]
  FuseRepRaw (s ': rest) = Append (FuseSector s) (FuseRepRaw rest)

-- | Full fusion of a 'Rep': same keys merged.
type family Fuse (rs :: Rep) :: Rep where
  Fuse rs = Coalesce (FuseRepRaw rs)

-- | CG channels for two atoms with attached multiplicity.
type family FuseAtoms (j1 :: Nat) (j2 :: Nat) (μ :: MultExpr) :: Rep where
  FuseAtoms j1 j2 μ = TagMult μ (AtomsFromCG (TensorIrrepRepSU2 j1 j2))

type family FuseAtomSpineOne (j1 :: Nat) (μ1 :: MultExpr) (q :: Rep) :: Rep where
  FuseAtomSpineOne _ _ '[] = '[]
  FuseAtomSpineOne j1 μ1 ('( 'Atom j2, 'AtomM m2) ': rest) =
    Append
      (FuseAtoms j1 j2 ('Prod μ1 ('AtomM m2)))
      (FuseAtomSpineOne j1 μ1 rest)

-- | Distribute atom spines and CG each pair.
type family FuseAtomSpines (r :: Rep) (q :: Rep) :: Rep where
  FuseAtomSpines '[] _ = '[]
  FuseAtomSpines ('( 'Atom j1, 'AtomM m1) ': rest) q =
    Append
      (FuseAtomSpineOne j1 ('AtomM m1) q)
      (FuseAtomSpines rest q)

-- | Fuse a 'RepExpr'. @'RTensor@ args must be atom @'RSum@ (non-recursive).
type family FuseExpr (e :: RepExpr) :: Rep where
  FuseExpr ('RSum rs) = Fuse rs
  FuseExpr ('RTensor ('RSum r) ('RSum q)) =
    Coalesce (FuseAtomSpines r q)

--------------------------------------------------------------------------------
-- Spine constraints
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
