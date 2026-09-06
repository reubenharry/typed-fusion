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
-- 'HomUnfused' indexes by 'Experiments.Fusion.Obj.Obj' trees
-- (@'Atom@ \/ @'Tensor@ \/ @'Sum@). 'HomFused' indexes by genealogy-preserving
-- 'TreeRep' (@'Leaf@ \/ @'Node@); 'FuseSym' still forgets @Obj@ to coalesced
-- 'Rep' for flat \/ Reference paths. Nested Mac Lane parenthesization lives on
-- @Obj@ (unfused) and on fusion trees (fused).
--
-- Sectors are keyed by bare @Nat@ (@2j@). Fusion trees ('Irrep' \/ 'TreeRep')
-- track genealogy in parallel with coalesced 'Rep'.
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
  , FlattenMult
  , FlattenRep
    -- * Coalesce (sorted merge)
  , InsertSector
  , InsertSectorOrd
  , Coalesce
  , FilterTrivial
    -- * Sector spaces
  , IrrepDim
  , ToVSector
  , ToVSpine
    -- * Obj spaces (true unfused)
  , ToVObj
    -- * Fusion trees (genealogy)
  , Root
  , ToVTree
  , ToVTreeRep
  , NodesFromCG
  , FuseTrees
  , FuseTreeRepOne
  , FuseTreeRep
  , ForgetTreeRep
  , FuseAssocL
  , FuseAssocR
  , FilterTrivialTrees
  , TreeUnit
  , FuseTreeRepU
  , CupMiddleTrees
    -- * Fusion (CG)
  , FuseRep
  , FuseHom
  , FuseFlat
  , AtomsFromCG
  , TagMult
  , FuseAtoms
  , FuseAtomSpineOne
  , FuseAtomSpines
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
import Math.LinearMap.Category (type (⊗))
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

-- | Collapse a multiplicity expression to a flat @'AtomM@.
type family FlattenMult (μ :: MultExpr) :: MultExpr where
  FlattenMult μ = 'AtomM (EvalMult μ)

-- | Flatten every sector's copy axis to @'AtomM@ (Symmetry @Nat@ mult layout).
-- Used by 'FuseFlat' / 'FuseRep' (not by 'FuseHom', which keeps @'Prod@ for cups).
type family FlattenRep (rs :: Rep) :: Rep where
  FlattenRep '[] = '[]
  FlattenRep ('(j, μ) ': rest) =
    '(j, FlattenMult μ) ': FlattenRep rest

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
-- Typical use: after 'Coalesce' \/ 'FuseHom', project to singlets (Hom space).
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

--------------------------------------------------------------------------------
-- Obj spaces (true unfused: Tensor = Kronecker, Sum = pair)
--------------------------------------------------------------------------------

-- | Interpret an @Obj@ tree as a nested space (no CG fuse).
type family ToVObj (a :: Obj Nat) :: Type where
  ToVObj ('FObj.Atom j) = ToVSector j ('AtomM 1)
  ToVObj ('FObj.Tensor a b) = ToVObj a ⊗ ToVObj b
  ToVObj ('FObj.Sum a b) = (ToVObj a, ToVObj b)

--------------------------------------------------------------------------------
-- Fusion trees: genealogy-preserving Irrep / TreeRep
--------------------------------------------------------------------------------

-- | Root @2j@ label of a fusion tree.
type family Root (t :: Irrep) :: Nat where
  Root ('Leaf j) = j
  Root ('Node j _ _) = j

-- | Space of one fusion tree: root irrep only (children are type indices).
type family ToVTree (t :: Irrep) :: Type where
  ToVTree t = C (IrrepDim (Root t))

-- | Forgetful direct-sum space of a 'TreeRep': right-nested root payloads.
-- Singleton @'[t]@ is just @ToVTree t@; longer lists nest pairs (same as 'ToVSpine').
type family ToVTreeRep (ts :: TreeRep) :: Type where
  ToVTreeRep '[t] = ToVTree t
  ToVTreeRep (t ': s ': rest) =
    (ToVTree t, ToVTreeRep (s ': rest))

-- | Attach children @t1@, @t2@ to every CG outcome label.
type family NodesFromCG (t1 :: Irrep) (t2 :: Irrep) (cg :: [(Nat, Nat)]) :: TreeRep where
  NodesFromCG _ _ '[] = '[]
  NodesFromCG t1 t2 ('(j, _) ': rest) =
    'Node j t1 t2 ': NodesFromCG t1 t2 rest

-- | CG fuse of two fusion trees: one @'Node@ per allowed total @2j@.
-- Same root ⇒ distinct trees (no coalesce); that /is/ the multiplicity basis.
type family FuseTrees (t1 :: Irrep) (t2 :: Irrep) :: TreeRep where
  FuseTrees t1 t2 =
    NodesFromCG t1 t2 (TensorIrrepRepSU2 (Root t1) (Root t2))

type family FuseTreeRepOne (t1 :: Irrep) (qs :: TreeRep) :: TreeRep where
  FuseTreeRepOne _ '[] = '[]
  FuseTreeRepOne t1 (t2 ': rest) =
    Append (FuseTrees t1 t2) (FuseTreeRepOne t1 rest)

-- | Cartesian fuse of two 'TreeRep' lists (distribute CG over pairs).
type family FuseTreeRep (rs :: TreeRep) (qs :: TreeRep) :: TreeRep where
  FuseTreeRep '[] _ = '[]
  FuseTreeRep (t1 ': rest) qs =
    Append (FuseTreeRepOne t1 qs) (FuseTreeRep rest qs)

-- | Forget genealogy: count trees by root into a coalesced 'Rep' (@'AtomM@).
-- Lossy — same-root trees become copy multiplicity.
type family ForgetTreeRep (ts :: TreeRep) :: Rep where
  ForgetTreeRep '[] = '[]
  ForgetTreeRep (t ': rest) =
    InsertSector (Root t) ('AtomM 1) (ForgetTreeRep rest)

-- | Left-associated triple fuse: @(a ⊗ b) ⊗ c@.
type FuseAssocL (a :: TreeRep) (b :: TreeRep) (c :: TreeRep) =
  FuseTreeRep (FuseTreeRep a b) c

-- | Right-associated triple fuse: @a ⊗ (b ⊗ c)@.
type FuseAssocR (a :: TreeRep) (b :: TreeRep) (c :: TreeRep) =
  FuseTreeRep a (FuseTreeRep b c)

-- | Keep only trees whose root is the trivial irrep (@0@).
type family FilterTrivialTrees (ts :: TreeRep) :: TreeRep where
  FilterTrivialTrees '[] = '[]
  FilterTrivialTrees ('Leaf 0 ': rest) = 'Leaf 0 ': FilterTrivialTrees rest
  FilterTrivialTrees ('Node 0 l r ': rest) =
    'Node 0 l r ': FilterTrivialTrees rest
  FilterTrivialTrees (_ ': rest) = FilterTrivialTrees rest

-- | Monoidal unit as a singleton tree list (bare trivial irrep).
type TreeUnit = '[ 'Leaf 0]

-- | Fuse with unitors (tree analogue of 'FuseRep').
type family FuseTreeRepU (a :: TreeRep) (b :: TreeRep) :: TreeRep where
  FuseTreeRepU '[ 'Leaf 0] b = b
  FuseTreeRepU a '[ 'Leaf 0] = a
  FuseTreeRepU a b = FuseTreeRep a b

-- | Cup-ready rewrite: drop a singlet middle from genealogy.
--
-- After @fmoveComposeTrees@, trees look like
-- @'Node j a ('Node jc ('Node 0 m1 m2) c)@. Contracting the @'Node 0@
-- middle yields @'Node j a c@ (SU(2) dual≅primal). Non-singlet middles drop.
type family CupMiddleTrees (ts :: TreeRep) :: TreeRep where
  CupMiddleTrees '[] = '[]
  CupMiddleTrees ('Node j a ('Node _jc ('Node 0 _m1 _m2) c) ': rest) =
    'Node j a c ': CupMiddleTrees rest
  CupMiddleTrees (_ ': rest) = CupMiddleTrees rest

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

-- | CG coalesce of two atom spines (no unitors).
--
-- * 'FuseHom' — raw coalesced fuse; keeps @'Prod@ copy tags (cups / Hom packing).
-- * 'FuseFlat' — @FlattenRep (FuseHom …)@; Symmetry @'AtomM@ layout (F-move).
-- * 'FuseRep' — monoidal product on 'FuseSym': unitors + 'FuseFlat' otherwise.
type FuseHom (r :: Rep) (q :: Rep) = Coalesce (FuseAtomSpines r q)

-- | Flattened fuse: every sector copy axis is @'AtomM@.
type FuseFlat (r :: Rep) (q :: Rep) = FlattenRep (FuseHom r q)

-- | Fused monoidal product of atom spines for 'FuseSym'.
type family FuseRep (a :: Rep) (b :: Rep) :: Rep where
  FuseRep '[ '(0, 'AtomM 1)] b = b
  FuseRep a '[ '(0, 'AtomM 1)] = a
  FuseRep a b = FuseFlat a b

-- | Forget a fusion-tree object (@Obj Nat@, @2j@ labels) to a coalesced 'Rep'
-- spine for Hom. Analogous to Fib @Fuse@\/@Mults@, but Hom is Dual-left @ToVSpine@.
type family FuseSym (a :: Obj Nat) :: Rep where
  FuseSym ('FObj.Atom j) = '[ '(j, 'AtomM 1)]
  FuseSym ('FObj.Tensor a b) = FuseRep (FuseSym a) (FuseSym b)
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
