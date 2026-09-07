{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Type-level spaces and fuse for symbolic SU(2).
--
-- 'HomUnfused' indexes by 'Experiments.Fusion.Obj.Obj' trees.
-- 'HomFused' indexes 'Obj Nat' (via 'ObjSpineSU2' / 'ObjRep' → leaf 'Rep');
-- morphisms are genealogy 'FuseRep' / 'RepV' (fusion-tree lists).
module Experiments.Symbolic.TypeLevel
  ( -- * Irrep dimension
    IrrepDim
    -- * Obj spaces (unfused)
  , ToVObj
    -- * Skeletal objects (HomFused)
  , Spine
  , ReplicateLeaf
  , SpineRep
  , ObjSpine
  , ObjSpineSU2
  , ObjRep
    -- * Fusion trees
  , Root
  , ToVTree
  , ToVRep
  , NodesFromCG
  , FuseTrees
  , FuseRepOne
  , FuseRep
  , FilterTrivial
  , Unit
  , UnitorCodomain
  ) where

import Data.Kind (Type)
import Experiments.Fusion.Obj (Obj, ObjSpine)
import qualified Experiments.Fusion.Obj as FObj
import Experiments.Fusion.SU2 (SU2Th)
import Experiments.Fusion.Unbounded (Spine)
import Experiments.SU2 (TensorIrrepRepSU2)
import Experiments.Symbolic.Expr
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
-- Obj spaces (true unfused: Tensor = Kronecker, Sum = pair)
--------------------------------------------------------------------------------

-- | Interpret an @Obj@ tree as a nested space (no CG fuse).
-- Atoms carry a trivial copy leg @C 1 ⊗ C (j+1)@ (unit multiplicity).
type family ToVObj (a :: Obj Nat) :: Type where
  ToVObj ('FObj.Atom j) = C 1 ⊗ C (IrrepDim j)
  ToVObj ('FObj.Tensor a b) = ToVObj a ⊗ ToVObj b
  ToVObj ('FObj.Sum a b) = (ToVObj a, ToVObj b)

--------------------------------------------------------------------------------
-- Skeletal objects → leaf Rep (HomFused object index)
--------------------------------------------------------------------------------

-- | @n@ copies of @'Leaf j@ (multiplicity expand).
type family ReplicateLeaf (n :: Nat) (j :: Nat) :: Rep where
  ReplicateLeaf 0 _j = '[]
  ReplicateLeaf 1 j = '[ 'Leaf j]
  ReplicateLeaf n j = 'Leaf j ': ReplicateLeaf (n - 1) j

-- | Expand a finite-support multiplicity spine to a leaf-only 'Rep'.
-- Order: spine order, @n@ consecutive @'Leaf j@ per sector.
type family SpineRep (sp :: Spine Nat) :: Rep where
  SpineRep '[] = '[]
  SpineRep ('(j, n) ': rest) =
    Append (ReplicateLeaf n j) (SpineRep rest)

-- | @Obj Nat → Spine Nat@ via SU(2) FuseNorm (no FiniteIrr).
type ObjSpineSU2 (a :: Obj Nat) = ObjSpine SU2Th a

-- | Leaf 'Rep' of an @Obj@ after skeletal fuse (@SpineRep ∘ ObjSpineSU2@).
type ObjRep (a :: Obj Nat) = SpineRep (ObjSpineSU2 a)

--------------------------------------------------------------------------------
-- Fusion trees: genealogy-preserving Irrep / Rep
--------------------------------------------------------------------------------

-- | Root @2j@ label of a fusion tree.
type family Root (t :: Irrep) :: Nat where
  Root ('Leaf j) = j
  Root ('Node j _ _) = j

-- | Space of one fusion tree: root irrep only (children are type indices).
type family ToVTree (t :: Irrep) :: Type where
  ToVTree t = C (IrrepDim (Root t))

-- | Forgetful direct-sum space of a 'Rep': right-nested root payloads.
type family ToVRep (ts :: Rep) :: Type where
  ToVRep '[t] = ToVTree t
  ToVRep (t ': s ': rest) =
    (ToVTree t, ToVRep (s ': rest))

-- | Attach children @t1@, @t2@ to every CG outcome label.
type family NodesFromCG (t1 :: Irrep) (t2 :: Irrep) (cg :: [(Nat, Nat)]) :: Rep where
  NodesFromCG _ _ '[] = '[]
  NodesFromCG t1 t2 ('(j, _) ': rest) =
    'Node j t1 t2 ': NodesFromCG t1 t2 rest

-- | CG fuse of two fusion trees: one @'Node@ per allowed total @2j@.
type family FuseTrees (t1 :: Irrep) (t2 :: Irrep) :: Rep where
  FuseTrees t1 t2 =
    NodesFromCG t1 t2 (TensorIrrepRepSU2 (Root t1) (Root t2))

type family FuseRepOne (t1 :: Irrep) (qs :: Rep) :: Rep where
  FuseRepOne _ '[] = '[]
  FuseRepOne t1 (t2 ': rest) =
    Append (FuseTrees t1 t2) (FuseRepOne t1 rest)

-- | Cartesian fuse of two 'Rep' lists (distribute CG over pairs).
type family FuseRep (rs :: Rep) (qs :: Rep) :: Rep where
  FuseRep '[] _ = '[]
  FuseRep (t1 ': rest) qs =
    Append (FuseRepOne t1 qs) (FuseRep rest qs)

-- | Monoidal unit as a singleton tree list (bare trivial irrep).
type Unit = '[ 'Leaf 0]

-- | Keep only total-charge-0 trees (SU(2) intertwiners / invariants).
--
-- Dispatches on @'CmpNat' j 0@ so @'CmpNat' j 0 ~ ''GT@ makes the drop
-- definitional (needed by 'FilterTrivialC').
type family FilterTrivial (ts :: Rep) :: Rep where
  FilterTrivial '[] = '[]
  FilterTrivial ('Leaf j ': rest) =
    FilterTrivialLeaf (CmpNat j 0) j rest
  FilterTrivial ('Node j l r ': rest) =
    FilterTrivialNode (CmpNat j 0) j l r rest

type family FilterTrivialLeaf (o :: Ordering) (j :: Nat) (rest :: Rep) :: Rep where
  FilterTrivialLeaf 'EQ _j rest = 'Leaf 0 ': FilterTrivial rest
  FilterTrivialLeaf 'GT _j rest = FilterTrivial rest
  FilterTrivialLeaf 'LT _j rest = FilterTrivial rest

type family FilterTrivialNode
  (o :: Ordering)
  (j :: Nat)
  (l :: Irrep)
  (r :: Irrep)
  (rest :: Rep)
  :: Rep
  where
  FilterTrivialNode 'EQ _j l r rest = 'Node 0 l r ': FilterTrivial rest
  FilterTrivialNode 'GT _j _l _r rest = FilterTrivial rest
  FilterTrivialNode 'LT _j _l _r rest = FilterTrivial rest

-- | Drop @Unit@ left children after @0 ⊗ t → t@:
-- @'Node _ ('Leaf 0) t ↦ t@.
type family UnitorCodomain (uc :: Rep) :: Rep where
  UnitorCodomain '[] = '[]
  UnitorCodomain ('Node _j ('Leaf 0) t ': rest) =
    t ': UnitorCodomain rest
