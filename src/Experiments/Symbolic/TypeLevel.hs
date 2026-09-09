{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Type-level spaces and fuse for symbolic SU(2).
--
-- 'HomUnfused' indexes by 'Experiments.Fusion.Obj.Obj' trees.
-- 'HomFused' indexes 'Obj Nat' (via 'ObjSpineSU2' / 'ObjRep' → bare 'Rep');
-- morphisms are genealogy 'FuseRep' / 'RepV' (fusion-tree lists).
-- 'ObjTrees' interprets an @Obj@ as a genealogy 'Rep' (@Norm@, then 'FuseRep').
module Experiments.Symbolic.TypeLevel
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
    -- * Genealogy Obj → Rep
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
import Experiments.Fusion.Obj (Norm, Obj, ObjSpine)
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
-- Atoms are bare irrep spaces @C (j+1)@; the monoidal unit is @C 1@.
type family ToVObj (a :: Obj Nat) :: Type where
  ToVObj ('FObj.Atom j) = C (IrrepDim j)
  ToVObj ('FObj.Tensor a b) = ToVObj a ⊗ ToVObj b
  ToVObj ('FObj.Sum a b) = (ToVObj a, ToVObj b)

--------------------------------------------------------------------------------
-- Skeletal objects → bare Rep (HomFused object index)
--------------------------------------------------------------------------------

-- | @n@ copies of @'I j@ (multiplicity expand).
type family ReplicateI (n :: Nat) (j :: Nat) :: Rep where
  ReplicateI 0 _j = '[]
  ReplicateI 1 j = '[ 'I j]
  ReplicateI n j = 'I j ': ReplicateI (n - 1) j

-- | Expand a finite-support multiplicity spine to a bare-only 'Rep'.
-- Order: spine order, @n@ consecutive @'I j@ per sector.
type family SpineRep (sp :: Spine Nat) :: Rep where
  SpineRep '[] = '[]
  SpineRep ('(j, n) ': rest) =
    Append (ReplicateI n j) (SpineRep rest)

-- | @Obj Nat → Spine Nat@ via SU(2) FuseNorm (no FiniteIrr).
type ObjSpineSU2 (a :: Obj Nat) = ObjSpine SU2Th a

-- | I 'Rep' of an @Obj@ after skeletal fuse (@SpineRep ∘ ObjSpineSU2@).
type ObjRep (a :: Obj Nat) = SpineRep (ObjSpineSU2 a)

--------------------------------------------------------------------------------
-- Genealogy Obj → Rep (association-preserving; distributes ⊗ over ⊕)
--------------------------------------------------------------------------------

-- | Interpret an @Obj@ tree as a genealogy 'Rep'.
--
-- First 'Norm' (distribute @⊗@ over @⊕@, flatten sums), then:
-- @'Atom j ↦ '[ 'I j]@, @'Tensor ↦ 'FuseRep@, @'Sum ↦ 'Append@.
type ObjTrees (a :: Obj Nat) = ObjTreesGo (Norm a)

type family ObjTreesGo (a :: Obj Nat) :: Rep where
  ObjTreesGo ('FObj.Atom j) = '[ 'I j]
  ObjTreesGo ('FObj.Tensor a b) =
    FuseRep (ObjTreesGo a) (ObjTreesGo b)
  ObjTreesGo ('FObj.Sum a b) =
    Append (ObjTreesGo a) (ObjTreesGo b)

--------------------------------------------------------------------------------
-- Fusion trees: genealogy-preserving Irrep / Rep
--------------------------------------------------------------------------------

-- | Root @2j@ label of a fusion tree.
type family Root (t :: Irrep) :: Nat where
  Root ('I j) = j
  Root ('From j '(_, _)) = j

-- | Space of one fusion tree: root irrep only (children are type indices).
type family ToVTree (t :: Irrep) :: Type where
  ToVTree t = C (IrrepDim (Root t))

-- | Forgetful direct-sum space of a 'Rep': right-nested root payloads.
type family ToVRep (ts :: Rep) :: Type where
  ToVRep '[t] = ToVTree t
  ToVRep (t ': s ': rest) =
    (ToVTree t, ToVRep (s ': rest))

-- | Attach children @t1@, @t2@ to every CG outcome label.
type family FromCG (t1 :: Irrep) (t2 :: Irrep) (cg :: [(Nat, Nat)]) :: Rep where
  FromCG _ _ '[] = '[]
  FromCG t1 t2 ('(j, _) ': rest) =
    'From j '(t1, t2) ': FromCG t1 t2 rest

-- | CG fuse of two fusion trees: one @'From@ per allowed total @2j@.
type family FuseTrees (t1 :: Irrep) (t2 :: Irrep) :: Rep where
  FuseTrees t1 t2 =
    FromCG t1 t2 (TensorIrrepRepSU2 (Root t1) (Root t2))

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
type Unit = '[ 'I 0]

-- | Keep only total-charge-0 trees (SU(2) intertwiners / invariants).
--
-- Dispatches on @'CmpNat' j 0@ so @'CmpNat' j 0 ~ ''GT@ makes the drop
-- definitional (needed by 'FilterTrivialC').
type family FilterTrivial (ts :: Rep) :: Rep where
  FilterTrivial '[] = '[]
  FilterTrivial ('I j ': rest) =
    FilterTrivialI (CmpNat j 0) j rest
  FilterTrivial ('From j '(l, r) ': rest) =
    FilterTrivialFrom (CmpNat j 0) j l r rest

type family FilterTrivialI (o :: Ordering) (j :: Nat) (rest :: Rep) :: Rep where
  FilterTrivialI 'EQ _j rest = 'I 0 ': FilterTrivial rest
  FilterTrivialI 'GT _j rest = FilterTrivial rest
  FilterTrivialI 'LT _j rest = FilterTrivial rest

type family FilterTrivialFrom
  (o :: Ordering)
  (j :: Nat)
  (l :: Irrep)
  (r :: Irrep)
  (rest :: Rep)
  :: Rep
  where
  FilterTrivialFrom 'EQ _j l r rest = 'From 0 '(l, r) ': FilterTrivial rest
  FilterTrivialFrom 'GT _j _l _r rest = FilterTrivial rest
  FilterTrivialFrom 'LT _j _l _r rest = FilterTrivial rest

-- | Drop @Unit@ left children after @0 ⊗ t → t@:
-- @'From _ '( 'I 0, t) ↦ t@.
type family UnitorCodomain (uc :: Rep) :: Rep where
  UnitorCodomain '[] = '[]
  UnitorCodomain ('From _j '( 'I 0, t) ': rest) =
    t ': UnitorCodomain rest
