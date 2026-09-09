{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Type-level spaces and fuse for symbolic SU(2).
--
-- 'HomUnfused' indexes by 'Fusion.Obj.Obj' trees.
-- 'HomFused' indexes 'Obj Nat' (via 'ObjSpineSU2' / 'ObjRep' → bare 'FTrees');
-- morphisms are genealogy 'FuseRep' / 'RepV' (fusion-tree lists).
-- 'ObjTrees' interprets an @Obj@ as a genealogy 'FTrees' (@Norm@, then 'FuseRep').
module Hom.TypeLevel
  ( -- * Irrep dimension
    IrrepDim
    -- * Obj spaces (unfused)
  , ToVObj
    -- * Skeletal objects (HomFused)
  , Spine
  , ReplicateI
  , SpineRep
  , ObjSpine
  , ObjSpineSU2
  , ObjRep
    -- * Genealogy Obj → FTrees
  , ObjTrees
    -- * Fusion trees
  , Root
  , ToVTree
  , ToVRep
  , FromCG
  , FuseTrees
  , FuseRepOne
  , FuseRep
  , FilterTrivial
  , Unit
  , UnitorCodomain
  ) where

import Data.Kind (Type)
import Fusion.Obj (Norm, Obj, ObjSpine)
import qualified Fusion.Obj as FObj
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
-- Obj spaces (true unfused: Tensor = Kronecker, Sum = pair)
--------------------------------------------------------------------------------

-- | Interpret an @Obj@ tree as a nested space (no CG fuse).
-- Atoms are bare irrep spaces @C (j+1)@; the monoidal unit is @C 1@.
type family ToVObj (a :: Obj Nat) :: Type where
  ToVObj ('FObj.Atom j) = C (IrrepDim j)
  ToVObj ('FObj.Tensor a b) = ToVObj a ⊗ ToVObj b
  ToVObj ('FObj.Sum a b) = (ToVObj a, ToVObj b)

--------------------------------------------------------------------------------
-- Skeletal objects → bare FTrees (HomFused object index)
--------------------------------------------------------------------------------

-- | @n@ copies of @'I j@ (multiplicity expand).
type family ReplicateI (n :: Nat) (j :: Nat) :: FTrees where
  ReplicateI 0 _j = '[]
  ReplicateI 1 j = '[ 'I j]
  ReplicateI n j = 'I j ': ReplicateI (n - 1) j

-- | Expand a finite-support multiplicity spine to a bare-only 'FTrees'.
-- Order: spine order, @n@ consecutive @'I j@ per sector.
type family SpineRep (sp :: Spine Nat) :: FTrees where
  SpineRep '[] = '[]
  SpineRep ('(j, n) ': rest) =
    Append (ReplicateI n j) (SpineRep rest)

-- | @Obj Nat → Spine Nat@ via SU(2) FuseNorm (no FiniteIrr).
type ObjSpineSU2 (a :: Obj Nat) = ObjSpine SU2Th a

-- | I 'FTrees' of an @Obj@ after skeletal fuse (@SpineRep ∘ ObjSpineSU2@).
type ObjRep (a :: Obj Nat) = SpineRep (ObjSpineSU2 a)

--------------------------------------------------------------------------------
-- Genealogy Obj → FTrees (association-preserving; distributes ⊗ over ⊕)
--------------------------------------------------------------------------------

-- | Interpret an @Obj@ tree as a genealogy 'FTrees'.
--
-- First 'Norm' (distribute @⊗@ over @⊕@, flatten sums), then:
-- @'Atom j ↦ '[ 'I j]@, @'Tensor ↦ 'FuseRep@, @'Sum ↦ 'Append@.
type ObjTrees (a :: Obj Nat) = ObjTreesGo (Norm a)

type family ObjTreesGo (a :: Obj Nat) :: FTrees where
  ObjTreesGo ('FObj.Atom j) = '[ 'I j]
  ObjTreesGo ('FObj.Tensor a b) =
    FuseRep (ObjTreesGo a) (ObjTreesGo b)
  ObjTreesGo ('FObj.Sum a b) =
    Append (ObjTreesGo a) (ObjTreesGo b)

--------------------------------------------------------------------------------
-- Fusion trees: genealogy-preserving FTree / FTrees
--------------------------------------------------------------------------------

-- | Root @2j@ label of a fusion tree.
type family Root (t :: FTree) :: Nat where
  Root ('I j) = j
  Root ('From j '(_, _)) = j

-- | Space of one fusion tree: root irrep only (children are type indices).
type family ToVTree (t :: FTree) :: Type where
  ToVTree t = C (IrrepDim (Root t))

-- | Forgetful direct-sum space of a 'FTrees': right-nested root payloads.
type family ToVRep (ts :: FTrees) :: Type where
  ToVRep '[t] = ToVTree t
  ToVRep (t ': s ': rest) =
    (ToVTree t, ToVRep (s ': rest))

-- | Attach children @t1@, @t2@ to every CG outcome label.
type family FromCG (t1 :: FTree) (t2 :: FTree) (cg :: [(Nat, Nat)]) :: FTrees where
  FromCG _ _ '[] = '[]
  FromCG t1 t2 ('(j, _) ': rest) =
    'From j '(t1, t2) ': FromCG t1 t2 rest

-- | CG fuse of two fusion trees: one @'From@ per allowed total @2j@.
type family FuseTrees (t1 :: FTree) (t2 :: FTree) :: FTrees where
  FuseTrees t1 t2 =
    FromCG t1 t2 (TensorIrrepRepSU2 (Root t1) (Root t2))

type family FuseRepOne (t1 :: FTree) (qs :: FTrees) :: FTrees where
  FuseRepOne _ '[] = '[]
  FuseRepOne t1 (t2 ': rest) =
    Append (FuseTrees t1 t2) (FuseRepOne t1 rest)

-- | Cartesian fuse of two 'FTrees' lists (distribute CG over pairs).
type family FuseRep (rs :: FTrees) (qs :: FTrees) :: FTrees where
  FuseRep '[] _ = '[]
  FuseRep (t1 ': rest) qs =
    Append (FuseRepOne t1 qs) (FuseRep rest qs)

-- | Monoidal unit as a singleton tree list (bare trivial irrep).
type Unit = '[ 'I 0]

-- | Keep only total-charge-0 trees (SU(2) intertwiners / invariants).
--
-- Dispatches on @'CmpNat' j 0@ so @'CmpNat' j 0 ~ ''GT@ makes the drop
-- definitional (needed by 'FilterTrivialC').
type family FilterTrivial (ts :: FTrees) :: FTrees where
  FilterTrivial '[] = '[]
  FilterTrivial ('I j ': rest) =
    FilterTrivialI (CmpNat j 0) j rest
  FilterTrivial ('From j '(l, r) ': rest) =
    FilterTrivialFrom (CmpNat j 0) j l r rest

type family FilterTrivialI (o :: Ordering) (j :: Nat) (rest :: FTrees) :: FTrees where
  FilterTrivialI 'EQ _j rest = 'I 0 ': FilterTrivial rest
  FilterTrivialI 'GT _j rest = FilterTrivial rest
  FilterTrivialI 'LT _j rest = FilterTrivial rest

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
-- @'From _ '( 'I 0, t) ↦ t@.
type family UnitorCodomain (uc :: FTrees) :: FTrees where
  UnitorCodomain '[] = '[]
  UnitorCodomain ('From _j '( 'I 0, t) ': rest) =
    t ': UnitorCodomain rest
