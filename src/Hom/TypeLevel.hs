{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Type-level spaces and fuse for group-indexed symbolic Hom.
--
-- 'HomUnfused' / 'HomFused' take @g :: Group@. Genealogy 'FuseFTrees' on @Nat@
-- labels remains the SU(2) engine; @ObjFTrees g@ selects it via 'TheoryOf'.
module Hom.TypeLevel
  ( -- * Group → fusion theory
    TheoryOf
    -- * Irrep dimension (SU(2) Nat genealogy)
  , IrrepDim
    -- * Obj spaces (unfused)
  , ToVObj
    -- * Skeletal objects (HomFused)
  , Spine
  , ReplicateIrrep
  , SpineFTrees
  , ObjSpine
  , ObjFTrees
    -- * Genealogy Obj → FTrees
  , ObjTrees
    -- * Fusion trees (Nat genealogy engine; SU(2))
  , Root
  , LabDim
  , LabCarrier
  , ToVTree
  , ToVFTrees
  , FromCG
  , FuseTrees
  , FuseFTreesOne
  , FuseFTrees
  , FilterTrivial
  , Unit
  , UnitorCodomain
  -- * U(1) genealogy (Z labels)
  , FuseTreesU1
  , FuseFTreesU1
  , FilterTrivialU1
  , UnitU1
  , ToVTreeU1
  , ToVFTreesU1
    -- * Obj space views (unfused / fused / trivial sector)
  , Unfused
  , Fused
  , Sym
  ) where

import Data.Kind (Type)
import Fusion.Obj (Norm, Obj (Irrep, (:⊗:), (:⊕:)), ObjSpine, ObjSpineZ)
import Fusion.SU2 (SU2Th)
import Fusion.U1 (U1Th)
import Fusion.Unbounded (Spine)
import Hom.Expr
import Symmetry.Group (Group (..), Irreps)
import Symmetry.Tensor (TensorIrrepRepSU2)
import GHC.TypeLits (CmpNat, Nat, type (+), type (-))
import Math.LinearMap.Category (type (⊗))
import Numeric.LinearAlgebra.Static (C)
import Symmetry.Utils (Append, Z (..))
import Fusion.Theory (FusionTheory (..))

--------------------------------------------------------------------------------
-- Irrep dimension (SU(2) Nat genealogy; matches fuseCGChannel's @j+1@)
--------------------------------------------------------------------------------

-- | SU(2) irrep dimension @j ↦ j + 1@ (local Nat form for genealogy / CG).
type family IrrepDim (j :: Nat) :: Nat where
  IrrepDim j = j + 1

--------------------------------------------------------------------------------
-- Group → fusion theory tag
--------------------------------------------------------------------------------

-- | Bridge @Group@ to 'FusionTheory' phantom tags.
type family TheoryOf (g :: Group) :: Type where
  TheoryOf SU2 = SU2Th
  TheoryOf U1 = U1Th

--------------------------------------------------------------------------------
-- Obj spaces (true unfused: :⊗: = Kronecker, :⊕: = pair)
--------------------------------------------------------------------------------

-- | Interpret an @Obj@ tree as a nested space (no CG fuse).
-- Per-group equations: matching on @Obj (Irreps g)@ is illegal when @Irreps@ is a family.
type family ToVObj (g :: Group) (a :: Obj (Irreps g)) :: Type where
  ToVObj SU2 ('Irrep j) = C (IrrepDim j)
  ToVObj SU2 ((a :⊗: b)) = ToVObj SU2 a ⊗ ToVObj SU2 b
  ToVObj SU2 ((a :⊕: b)) = (ToVObj SU2 a, ToVObj SU2 b)
  ToVObj U1 ('Irrep _) = C 1
  ToVObj U1 ((a :⊗: b)) = ToVObj U1 a ⊗ ToVObj U1 b
  ToVObj U1 ((a :⊕: b)) = (ToVObj U1 a, ToVObj U1 b)

-- | Object-space views of an @Obj@ (vector spaces — not Hom morphisms).
type Unfused (g :: Group) (a :: Obj (Irreps g)) = ToVObj g a

type family Fused (g :: Group) (a :: Obj (Irreps g)) :: Type where
  Fused SU2 a = ToVFTrees (ObjTrees SU2 a)
  Fused U1 a = ToVFTrees (ObjTrees U1 a)

type family Sym (g :: Group) (a :: Obj (Irreps g)) :: Type where
  Sym SU2 a = ToVFTrees (FilterTrivial (ObjTrees SU2 a))
  Sym U1 a = ToVFTrees (FilterTrivialU1 (ObjTrees U1 a))

--------------------------------------------------------------------------------
-- Skeletal objects → bare FTrees (HomFused object index)
--------------------------------------------------------------------------------

-- | @n@ copies of @'IrrepTree j@ (multiplicity expand).
type family ReplicateIrrep (n :: Nat) (j :: Nat) :: FTrees Nat where
  ReplicateIrrep 0 _j = '[]
  ReplicateIrrep 1 j = '[ 'IrrepTree j]
  ReplicateIrrep n j = 'IrrepTree j ': ReplicateIrrep (n - 1) j

type family ReplicateIrrepZ (n :: Nat) (j :: Z) :: FTrees Z where
  ReplicateIrrepZ 0 _j = '[]
  ReplicateIrrepZ 1 j = '[ 'IrrepTree j]
  ReplicateIrrepZ n j = 'IrrepTree j ': ReplicateIrrepZ (n - 1) j

-- | Expand a finite-support multiplicity spine to a bare-only 'FTrees'.
type family SpineFTrees (sp :: Spine Nat) :: FTrees Nat where
  SpineFTrees '[] = '[]
  SpineFTrees ('(j, n) ': rest) =
    Append (ReplicateIrrep n j) (SpineFTrees rest)

type family SpineFTreesZ (sp :: Spine Z) :: FTrees Z where
  SpineFTreesZ '[] = '[]
  SpineFTreesZ ('(j, n) ': rest) =
    Append (ReplicateIrrepZ n j) (SpineFTreesZ rest)

-- | Bare 'FTrees' of an @Obj@ after skeletal fuse.
type family ObjFTrees (g :: Group) (a :: Obj (Irreps g)) :: FTrees (Irreps g) where
  ObjFTrees SU2 a = SpineFTrees (ObjSpine SU2Th a)
  ObjFTrees U1 a = SpineFTreesZ (ObjSpineZ U1Th a)

--------------------------------------------------------------------------------
-- Genealogy Obj → FTrees (association-preserving; distributes ⊗ over ⊕)
--------------------------------------------------------------------------------

type family ObjTrees (g :: Group) (a :: Obj (Irreps g)) :: FTrees (Irreps g) where
  ObjTrees SU2 a = ObjTreesGo (Norm a)
  ObjTrees U1 a = ObjTreesGoU1 (Norm a)

type family ObjTreesGo (a :: Obj Nat) :: FTrees Nat where
  ObjTreesGo ('Irrep j) = '[ 'IrrepTree j]
  ObjTreesGo ((a :⊗: b)) =
    FuseFTrees (ObjTreesGo a) (ObjTreesGo b)
  ObjTreesGo ((a :⊕: b)) =
    Append (ObjTreesGo a) (ObjTreesGo b)

type family ObjTreesGoU1 (a :: Obj Z) :: FTrees Z where
  ObjTreesGoU1 ('Irrep j) = '[ 'IrrepTree j]
  ObjTreesGoU1 ((a :⊗: b)) =
    FuseFTreesU1 (ObjTreesGoU1 a) (ObjTreesGoU1 b)
  ObjTreesGoU1 ((a :⊕: b)) =
    Append (ObjTreesGoU1 a) (ObjTreesGoU1 b)

--------------------------------------------------------------------------------
-- Fusion trees: genealogy-preserving FTree / FTrees (Nat / SU(2) engine)
--------------------------------------------------------------------------------

type family Root (t :: FTree lab) :: lab where
  Root ('IrrepTree j) = j
  Root ('From j '(_, _)) = j

-- | Carrier dimension of a root label: SU(2) @j+1@, U(1) @1@.
type family LabDim (j :: k) :: Nat where
  LabDim (j :: Nat) = IrrepDim j
  LabDim (_ :: Z) = 1

-- | Carrier of a root label: @C (LabDim j)@.
type LabCarrier (j :: k) = C (LabDim j)

-- | Space of one fusion tree: root irrep carrier (label-polymorphic).
type family ToVTree (t :: FTree lab) :: Type where
  ToVTree t = LabCarrier (Root t)

type family ToVFTrees (ts :: FTrees lab) :: Type where
  ToVFTrees '[t] = ToVTree t
  ToVFTrees (t ': s ': rest) =
    (ToVTree t, ToVFTrees (s ': rest))

type family FromCG (t1 :: FTree lab) (t2 :: FTree lab) (cg :: [(lab, Nat)]) :: FTrees lab where
  FromCG _ _ '[] = '[]
  FromCG t1 t2 ('(j, _) ': rest) =
    'From j '(t1, t2) ': FromCG t1 t2 rest

type family FuseTrees (t1 :: FTree Nat) (t2 :: FTree Nat) :: FTrees Nat where
  FuseTrees t1 t2 =
    FromCG t1 t2 (TensorIrrepRepSU2 (Root t1) (Root t2))

type family FuseFTreesOne (t1 :: FTree Nat) (qs :: FTrees Nat) :: FTrees Nat where
  FuseFTreesOne _ '[] = '[]
  FuseFTreesOne t1 (t2 ': rest) =
    Append (FuseTrees t1 t2) (FuseFTreesOne t1 rest)

type family FuseFTrees (rs :: FTrees Nat) (qs :: FTrees Nat) :: FTrees Nat where
  FuseFTrees '[] _ = '[]
  FuseFTrees (t1 ': rest) qs =
    Append (FuseFTreesOne t1 qs) (FuseFTrees rest qs)

type Unit = '[ 'IrrepTree 0] :: FTrees Nat

type family FilterTrivial (ts :: FTrees Nat) :: FTrees Nat where
  FilterTrivial '[] = '[]
  FilterTrivial ('IrrepTree j ': rest) =
    FilterTrivialIrrep (CmpNat j 0) j rest
  FilterTrivial ('From j '(l, r) ': rest) =
    FilterTrivialFrom (CmpNat j 0) j l r rest

type family FilterTrivialIrrep (o :: Ordering) (j :: Nat) (rest :: FTrees Nat) :: FTrees Nat where
  FilterTrivialIrrep 'EQ _j rest = 'IrrepTree 0 ': FilterTrivial rest
  FilterTrivialIrrep 'GT _j rest = FilterTrivial rest
  FilterTrivialIrrep 'LT _j rest = FilterTrivial rest

type family FilterTrivialFrom
  (o :: Ordering)
  (j :: Nat)
  (l :: FTree Nat)
  (r :: FTree Nat)
  (rest :: FTrees Nat)
  :: FTrees Nat
  where
  FilterTrivialFrom 'EQ _j l r rest = 'From 0 '(l, r) ': FilterTrivial rest
  FilterTrivialFrom 'GT _j _l _r rest = FilterTrivial rest
  FilterTrivialFrom 'LT _j _l _r rest = FilterTrivial rest

type family UnitorCodomain (uc :: FTrees Nat) :: FTrees Nat where
  UnitorCodomain '[] = '[]
  UnitorCodomain ('From _j '( 'IrrepTree 0, t) ': rest) =
    t ': UnitorCodomain rest

--------------------------------------------------------------------------------
-- U(1) genealogy engine (Z labels)
--------------------------------------------------------------------------------

-- | U(1) synonyms for the label-polymorphic carriers.
type ToVTreeU1 (t :: FTree Z) = ToVTree t
type ToVFTreesU1 (ts :: FTrees Z) = ToVFTrees ts

type family FuseTreesU1 (t1 :: FTree Z) (t2 :: FTree Z) :: FTrees Z where
  FuseTreesU1 t1 t2 =
    FromCG t1 t2 (FuseN U1Th (Root t1) (Root t2))

type family FuseFTreesOneU1 (t1 :: FTree Z) (qs :: FTrees Z) :: FTrees Z where
  FuseFTreesOneU1 _ '[] = '[]
  FuseFTreesOneU1 t1 (t2 ': rest) =
    Append (FuseTreesU1 t1 t2) (FuseFTreesOneU1 t1 rest)

type family FuseFTreesU1 (rs :: FTrees Z) (qs :: FTrees Z) :: FTrees Z where
  FuseFTreesU1 '[] _ = '[]
  FuseFTreesU1 (t1 ': rest) qs =
    Append (FuseFTreesOneU1 t1 qs) (FuseFTreesU1 rest qs)

type UnitU1 = '[ 'IrrepTree 'Zero] :: FTrees Z

-- | Keep total-charge-0 trees (U(1) intertwiners).
type family FilterTrivialU1 (ts :: FTrees Z) :: FTrees Z where
  FilterTrivialU1 '[] = '[]
  FilterTrivialU1 ('IrrepTree 'Zero ': rest) =
    'IrrepTree 'Zero ': FilterTrivialU1 rest
  FilterTrivialU1 ('IrrepTree _ ': rest) = FilterTrivialU1 rest
  FilterTrivialU1 ('From 'Zero '(l, r) ': rest) =
    'From 'Zero '(l, r) ': FilterTrivialU1 rest
  FilterTrivialU1 ('From _ '(l, r) ': rest) = FilterTrivialU1 rest
