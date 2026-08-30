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
-- 'RepExpr' is the @ToV@ / space layer (unfused Kronecker, duals, 'MorExpr'
-- packing) — not the categorical object kind. Categorical objects for 'Sym'
-- are 'Experiments.Fusion.Obj.Obj' trees (@'Atom@ \/ @'Tensor@ \/ @'Sum@);
-- 'FuseSym' forgets them to a coalesced 'Rep' spine for Hom.
--
-- Sectors are keyed by bare @Nat@ (@2j@). Unfused tensor and dual spaces use
-- 'RepExpr' (@'RTensor@ / @'RDual@) and reduce via 'FuseExpr' / 'ToV'. Nested
-- Mac Lane parenthesization lives on @Obj@, not on 'RepExpr' (well-formed
-- @'RTensor@ stays binary on atom @'RSum@ spines).
module Experiments.Symbolic.TypeLevel
  ( -- * Braid
    BraidMult
  , BraidSector
  , Braid
    -- * Unit
  , Unit
    -- * Multiplicity
  , EvalMult
  , AddMult
    -- * Coalesce (sorted merge)
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
  , DualExpr
  , MorExpr
  , MorExprFused
  , CupUnfusedExpr
  , CapUnfusedExpr
  , CupFusedRep
  , CapFusedRep
    -- * Fusion (CG)
  , FuseExpr
  , AtomsFromCG
  , TagMult
  , FuseAtoms
  , FuseAtomSpineOne
  , FuseAtomSpines
  , SymTensor
  , FuseSym
    -- * Spine constraints
  , AtomSpine
  ) where

import Data.Kind (Constraint, Type)
import Experiments.Fusion.Obj (Obj)
import qualified Experiments.Fusion.Obj as FObj
import Experiments.SU2 (TensorIrrepRepSU2)
import Experiments.Symbolic.Expr
import GHC.TypeLits (CmpNat, KnownNat, Nat, type (*), type (+))
import Math.LinearMap.Category (DualVector, type (⊗))
import Numeric.LinearAlgebra.Static (C)
import Symmetry.Utils (Append)

-- Braid (swap copy factors on each sector)
--------------------------------------------------------------------------------

type family BraidMult (μ :: MultExpr) :: MultExpr where
  BraidMult ('AtomM m) = 'AtomM m
  BraidMult ('Prod μ1 μ2) = 'Prod (BraidMult μ2) (BraidMult μ1)

type family BraidSector (s :: Sector) :: Sector where
  BraidSector '(j, μ) = '(j, BraidMult μ)

-- | Braid every sector in a spine (swap the @'Prod@ copy factors).
type family Braid (rs :: Rep) :: Rep where
  Braid '[] = '[]
  Braid (s ': rs) = BraidSector s ': Braid rs

-- | Monoidal unit: trivial irrep @j = 0@ with unit multiplicity.
type Unit = '[ '(0, 'AtomM 1)]

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
-- Coalesce: sort + merge sectors with equal irrep label
--------------------------------------------------------------------------------

-- | Insert one sector into an already-coalesced (sorted, merged) spine.
type family InsertSector (j :: Nat) (μ :: MultExpr) (rs :: Rep) :: Rep where
  InsertSector j μ '[] = '[ '(j, μ)]
  InsertSector j μ ('(j2, μ2) ': rest) =
    InsertSectorOrd (CmpNat j j2) j μ j2 μ2 rest

type family InsertSectorOrd
  (o :: Ordering)
  (j :: Nat) (μ :: MultExpr)
  (j2 :: Nat) (μ2 :: MultExpr)
  (rest :: Rep)
  :: Rep
 where
  InsertSectorOrd 'EQ j μ _ μ2 rest = '(j, AddMult μ μ2) ': rest
  InsertSectorOrd 'LT j μ j2 μ2 rest = '(j, μ) ': '(j2, μ2) ': rest
  InsertSectorOrd 'GT j μ j2 μ2 rest = '(j2, μ2) ': InsertSector j μ rest

-- | Fold @InsertSector@ over a raw spine → sorted, merged 'Rep'.
type family Coalesce (rs :: Rep) :: Rep where
  Coalesce '[] = '[]
  Coalesce ('(j, μ) ': rest) = InsertSector j μ (Coalesce rest)

-- | Keep only the SU(2) trivial irrep (@0@); drop everything else.
-- Typical use: after 'Coalesce' \/ 'FuseExpr', project to singlets (Hom space).
type family FilterTrivial (rs :: Rep) :: Rep where
  FilterTrivial '[] = '[]
  FilterTrivial ('(0, μ) ': rest) = '(0, μ) ': FilterTrivial rest
  FilterTrivial ('(j, μ) ': rest) = FilterTrivial rest

--------------------------------------------------------------------------------
-- Sector spaces (concrete vectors indexed by irrep / multiplicity)
--------------------------------------------------------------------------------

-- | SU(2) irrep dimension @j ↦ j + 1@.
type family IrrepDim (j :: Nat) :: Nat where
  IrrepDim j = j + 1

-- | Sector space from irrep label + multiplicity.
type family ToVSector (j :: Nat) (μ :: MultExpr) :: Type where
  ToVSector j ('AtomM m) = C m ⊗ C (IrrepDim j)
  ToVSector j ('Prod ('AtomM m) ('AtomM n)) =
    (C m ⊗ C n) ⊗ C (IrrepDim j)

-- | Forgetful direct-sum space of a spine: right-nested sector payloads.
--
-- Singleton @'[s]@ is just @ToVSector s@; longer spines are
-- @(ToVSector s1, ToVSpine rest)@ (no @()@ terminator — that breaks
-- linearmap @Scalar@ / @⊗@). Empty spine is unsupported as an @LSpace@.
type family ToVSpine (rs :: Rep) :: Type where
  ToVSpine '[ '(j, μ) ] = ToVSector j μ
  ToVSpine ('(j, μ) ': s ': rest) =
    (ToVSector j μ, ToVSpine (s ': rest))

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

-- | Fused Hom @r → q@: @'RSum@ of @FuseExpr (MorExpr r q)@.
--
-- For SU(2) atom spines, dual≅primal at the type level, so this is the same
-- coalesced CG spine as @FuseExpr ('RTensor ('RSum r) ('RSum q))@.
type MorExprFused (r :: Rep) (q :: Rep) =
  'RSum (FuseExpr (MorExpr r q))

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
-- Fusion: CG on atom pairs, then coalesced rep
--------------------------------------------------------------------------------

-- | Tag every CG channel with unit multiplicity (irrep-only fuse).
type family AtomsFromCG (cg :: [(Nat, Nat)]) :: Rep where
  AtomsFromCG '[] = '[]
  AtomsFromCG ('(j, _) ': rest) = '(j, 'AtomM 1) ': AtomsFromCG rest

-- | Attach a sector multiplicity to every atom in a fused irrep spine.
type family TagMult (μ :: MultExpr) (rs :: Rep) :: Rep where
  TagMult μ '[] = '[]
  TagMult μ ('(j, _) ': rest) = '(j, μ) ': TagMult μ rest

-- | CG channels for two atoms with attached multiplicity.
type family FuseAtoms (j1 :: Nat) (j2 :: Nat) (μ :: MultExpr) :: Rep where
  FuseAtoms j1 j2 μ = TagMult μ (AtomsFromCG (TensorIrrepRepSU2 j1 j2))

type family FuseAtomSpineOne (j1 :: Nat) (μ1 :: MultExpr) (q :: Rep) :: Rep where
  FuseAtomSpineOne _ _ '[] = '[]
  FuseAtomSpineOne j1 μ1 ('(j2, 'AtomM m2) ': rest) =
    Append
      (FuseAtoms j1 j2 ('Prod μ1 ('AtomM m2)))
      (FuseAtomSpineOne j1 μ1 rest)

-- | Distribute atom spines and CG each pair.
type family FuseAtomSpines (r :: Rep) (q :: Rep) :: Rep where
  FuseAtomSpines '[] _ = '[]
  FuseAtomSpines ('(j1, 'AtomM m1) ': rest) q =
    Append
      (FuseAtomSpineOne j1 ('AtomM m1) q)
      (FuseAtomSpines rest q)

-- | Fuse a 'RepExpr' to a coalesced 'Rep'.
--
-- @
--   'RSum rs              ↦  Coalesce rs          -- already atom spine
--   'RTensor ('RSum r) ('RSum q)  ↦  CG coalesce   -- real fuse
--   Dual-left Hom tensors fuse like primal⊗primal (SU(2) dual≅primal)
-- @
type family FuseExpr (e :: RepExpr) :: Rep where
  FuseExpr ('RSum rs) = Coalesce rs
  FuseExpr ('RTensor ('RSum r) ('RSum q)) =
    Coalesce (FuseAtomSpines r q)
  FuseExpr ('RTensor ('RDual ('RSum r)) ('RSum q)) =
    Coalesce (FuseAtomSpines r q)

-- | Fused monoidal product of atom spines (@CG@ coalesce).
-- Unitor equations: @Unit ⊗ a = a = a ⊗ Unit@.
type family SymTensor (a :: Rep) (b :: Rep) :: Rep where
  SymTensor '[ '(0, 'AtomM 1)] b = b
  SymTensor a '[ '(0, 'AtomM 1)] = a
  SymTensor a b = FuseExpr ('RTensor ('RSum a) ('RSum b))

-- | Forget a fusion-tree object (@Obj Nat@, @2j@ labels) to a coalesced 'Rep'
-- spine for 'MorExpr' Hom. Analogous to Fib @Fuse@\/@Mults@, but the Hom
-- packing is Dual-left @ToV@ rather than finite-Irr @HomS@.
type family FuseSym (a :: Obj Nat) :: Rep where
  FuseSym ('FObj.Atom j) = '[ '(j, 'AtomM 1)]
  FuseSym ('FObj.Tensor a b) = SymTensor (FuseSym a) (FuseSym b)
  FuseSym ('FObj.Sum a b) = Coalesce (Append (FuseSym a) (FuseSym b))

--------------------------------------------------------------------------------
-- Spine constraints
--------------------------------------------------------------------------------

-- | Constraint: spine is leaf atoms with @'AtomM@ multiplicities (tensor domain).
type family AtomSpine (rs :: Rep) :: Constraint where
  AtomSpine '[] = ()
  AtomSpine ('(j, 'AtomM m) ': rest) =
    ( KnownNat j
    , KnownNat m
    , KnownNat (IrrepDim j)
    , AtomSpine rest
    )
