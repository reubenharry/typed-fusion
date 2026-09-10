{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Type-level spaces and fuse for symbolic SU(2).
--
-- 'HomUnfused' indexes by 'Fusion.Obj.Obj' trees.
-- 'HomFused' indexes 'Obj Nat' (via 'ObjSpineSU2' / 'ObjFTrees' → bare 'FTrees');
-- morphisms are genealogy 'FuseFTrees' / 'FTreeV' (fusion-tree lists).
-- 'ObjTrees' interprets an @Obj@ as a genealogy 'FTrees' (@Norm@, then 'FuseFTrees').
module Hom.TypeLevel
  ( -- * Irrep dimension
    IrrepDim
    -- * Obj spaces (unfused)
  , ToVObj
    -- * Skeletal objects (HomFused)
  , Spine
  , ReplicateIrrep
  , SpineFTrees
  , ObjSpine
  , ObjSpineSU2
  , ObjFTrees
    -- * Genealogy Obj → FTrees
  , ObjTrees
    -- * Fusion trees
  , Root
  , ToVTree
  , ToVFTrees
  , FromCG
  , FuseTrees
  , FuseFTreesOne
  , FuseFTrees
  , FilterTrivial
  , Unit
  , UnitorCodomain
    -- * Obj space views (unfused / fused / trivial sector)
  , Unfused
  , Fused
  , Sym
  ) where

import Data.Kind (Type)
import Fusion.Obj (Norm, Obj (Irrep, (:⊗:), (:⊕:)), ObjSpine)
import Fusion.SU2 (SU2Th)
import Fusion.Unbounded (Spine)
import Symmetry.Tensor (TensorIrrepRepSU2)
import Hom.Expr
import GHC.TypeLits (CmpNat, Nat, type (+), type (-))
import Math.LinearMap.Category (type (⊗))
import Numeric.LinearAlgebra.Static (C)
import Symmetry.Utils (Append)

--------------------------------------------------------------------------------
-- Irrep dimension
--------------------------------------------------------------------------------

-- | SU(2) irrep dimension @j ↦ j + 1@.
type family IrrepDim (j :: Nat) :: Nat where
  IrrepDim j = j + 1

--------------------------------------------------------------------------------
-- Obj spaces (true unfused: :⊗: = Kronecker, :⊕: = pair)
--------------------------------------------------------------------------------

-- | Interpret an @Obj@ tree as a nested space (no CG fuse).
-- Irreps are bare spaces @C (j+1)@; the monoidal unit is @C 1@.
type family ToVObj (a :: Obj Nat) :: Type where
  ToVObj ('Irrep j) = C (IrrepDim j)
  ToVObj ((a :⊗: b)) = ToVObj a ⊗ ToVObj b
  ToVObj ((a :⊕: b)) = (ToVObj a, ToVObj b)

-- | Object-space views of an @Obj@ (vector spaces — not Hom morphisms).
--
-- * 'Unfused' — Kronecker / pair packing ('ToVObj'); payload space for 'HomUnfused'.
-- * 'Fused' — genealogy spaces via 'ObjTrees' (association-preserving fuse trees).
-- * 'Sym' — trivial total-charge sector ('FilterTrivial' ∘ 'ObjTrees'); invariants.
type Unfused (a :: Obj Nat) = ToVObj a
type Fused (a :: Obj Nat) = ToVFTrees (ObjTrees a)
type Sym (a :: Obj Nat) = ToVFTrees (FilterTrivial (ObjTrees a))

--------------------------------------------------------------------------------
-- Skeletal objects → bare FTrees (HomFused object index)
--------------------------------------------------------------------------------

-- | @n@ copies of @'IrrepTree j@ (multiplicity expand).
type family ReplicateIrrep (n :: Nat) (j :: Nat) :: FTrees where
  ReplicateIrrep 0 _j = '[]
  ReplicateIrrep 1 j = '[ 'IrrepTree j]
  ReplicateIrrep n j = 'IrrepTree j ': ReplicateIrrep (n - 1) j

-- | Expand a finite-support multiplicity spine to a bare-only 'FTrees'.
-- Order: spine order, @n@ consecutive @'IrrepTree j@ per sector.
type family SpineFTrees (sp :: Spine Nat) :: FTrees where
  SpineFTrees '[] = '[]
  SpineFTrees ('(j, n) ': rest) =
    Append (ReplicateIrrep n j) (SpineFTrees rest)

-- | @Obj Nat → Spine Nat@ via SU(2) FuseNorm (no FiniteIrr).
type ObjSpineSU2 (a :: Obj Nat) = ObjSpine SU2Th a

-- | Bare 'FTrees' of an @Obj@ after skeletal fuse (@SpineFTrees ∘ ObjSpineSU2@).
type ObjFTrees (a :: Obj Nat) = SpineFTrees (ObjSpineSU2 a)

--------------------------------------------------------------------------------
-- Genealogy Obj → FTrees (association-preserving; distributes ⊗ over ⊕)
--------------------------------------------------------------------------------

-- | Interpret an @Obj@ tree as a genealogy 'FTrees'.
--
-- First 'Norm' (distribute @⊗@ over @⊕@, flatten sums), then:
-- @'Irrep j ↦ '[ 'IrrepTree j]@, @':⊗:' ↦ 'FuseFTrees@, @':⊕:' ↦ 'Append@.
type ObjTrees (a :: Obj Nat) = ObjTreesGo (Norm a)

type family ObjTreesGo (a :: Obj Nat) :: FTrees where
  ObjTreesGo ('Irrep j) = '[ 'IrrepTree j]
  ObjTreesGo ((a :⊗: b)) =
    FuseFTrees (ObjTreesGo a) (ObjTreesGo b)
  ObjTreesGo ((a :⊕: b)) =
    Append (ObjTreesGo a) (ObjTreesGo b)

--------------------------------------------------------------------------------
-- Fusion trees: genealogy-preserving FTree / FTrees
--------------------------------------------------------------------------------

-- | Root @2j@ label of a fusion tree.
type family Root (t :: FTree) :: Nat where
  Root ('IrrepTree j) = j
  Root ('From j '(_, _)) = j

-- | Space of one fusion tree: root irrep only (children are type indices).
type family ToVTree (t :: FTree) :: Type where
  ToVTree t = C (IrrepDim (Root t))

-- | Forgetful direct-sum space of a 'FTrees': right-nested root payloads.
type family ToVFTrees (ts :: FTrees) :: Type where
  ToVFTrees '[t] = ToVTree t
  ToVFTrees (t ': s ': rest) =
    (ToVTree t, ToVFTrees (s ': rest))

-- | Attach children @t1@, @t2@ to every CG outcome label.
type family FromCG (t1 :: FTree) (t2 :: FTree) (cg :: [(Nat, Nat)]) :: FTrees where
  FromCG _ _ '[] = '[]
  FromCG t1 t2 ('(j, _) ': rest) =
    'From j '(t1, t2) ': FromCG t1 t2 rest

-- | CG fuse of two fusion trees: one @'From@ per allowed total @2j@.
type family FuseTrees (t1 :: FTree) (t2 :: FTree) :: FTrees where
  FuseTrees t1 t2 =
    FromCG t1 t2 (TensorIrrepRepSU2 (Root t1) (Root t2))

type family FuseFTreesOne (t1 :: FTree) (qs :: FTrees) :: FTrees where
  FuseFTreesOne _ '[] = '[]
  FuseFTreesOne t1 (t2 ': rest) =
    Append (FuseTrees t1 t2) (FuseFTreesOne t1 rest)

-- | Cartesian fuse of two 'FTrees' lists (distribute CG over pairs).
type family FuseFTrees (rs :: FTrees) (qs :: FTrees) :: FTrees where
  FuseFTrees '[] _ = '[]
  FuseFTrees (t1 ': rest) qs =
    Append (FuseFTreesOne t1 qs) (FuseFTrees rest qs)

-- | Monoidal unit as a singleton tree list (bare trivial irrep).
type Unit = '[ 'IrrepTree 0]

-- | Keep only total-charge-0 trees (SU(2) intertwiners / invariants).
--
-- Dispatches on @'CmpNat' j 0@ so @'CmpNat' j 0 ~ ''GT@ makes the drop
-- definitional (needed by 'filterTrivialFTreeV' / 'embedTrivialFTreeV').
type family FilterTrivial (ts :: FTrees) :: FTrees where
  FilterTrivial '[] = '[]
  FilterTrivial ('IrrepTree j ': rest) =
    FilterTrivialIrrep (CmpNat j 0) j rest
  FilterTrivial ('From j '(l, r) ': rest) =
    FilterTrivialFrom (CmpNat j 0) j l r rest

type family FilterTrivialIrrep (o :: Ordering) (j :: Nat) (rest :: FTrees) :: FTrees where
  FilterTrivialIrrep 'EQ _j rest = 'IrrepTree 0 ': FilterTrivial rest
  FilterTrivialIrrep 'GT _j rest = FilterTrivial rest
  FilterTrivialIrrep 'LT _j rest = FilterTrivial rest

type family FilterTrivialFrom
  (o :: Ordering)
  (j :: Nat)
  (l :: FTree)
  (r :: FTree)
  (rest :: FTrees)
  :: FTrees
  where
  FilterTrivialFrom 'EQ _j l r rest = 'From 0 '(l, r) ': FilterTrivial rest
  FilterTrivialFrom 'GT _j _l _r rest = FilterTrivial rest
  FilterTrivialFrom 'LT _j _l _r rest = FilterTrivial rest

-- | Drop @Unit@ left children after @0 ⊗ t → t@:
-- @'From _ '( 'IrrepTree 0, t) ↦ t@.
type family UnitorCodomain (uc :: FTrees) :: FTrees where
  UnitorCodomain '[] = '[]
  UnitorCodomain ('From _j '( 'IrrepTree 0, t) ': rest) =
    t ': UnitorCodomain rest
