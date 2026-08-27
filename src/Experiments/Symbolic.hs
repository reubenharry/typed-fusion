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

-- | Green-field symbolic SU(2) reps: flat irrep @'Tensor ('Atom j1) ('Atom j2)@ and flat
-- multiplicity @'Prod ('AtomM m) ('AtomM n)@.
--
-- Fusion-tree association is temporal (@Fuse@ then tensor again), so tensors
-- are always leaf×leaf. 'Coalesce' merges same-'IrrepExpr' sectors by adding
-- evaluated multiplicities into an @'AtomM@. 'RepV' is the indexed term-level
-- spine; 'fuseRaw' / 'coalesce' fold it directly (no spine class).
--
-- __Merge layout (coalesced):__ same-'IrrepExpr' sectors combine by direct sum
-- along the copy axis via 'TensorNetwork.Categorical.mergeCopyAxis' (and
-- 'flattenCopyProd' / 'flattenTensorProdCopy' when a @'Prod'@ leg must
-- collapse to @'AtomM'@ first). Output multiplicity is always
-- @'AtomM (EvalMult μ1 + …)@.
--
-- Tensor CG fuse uses typed 'Symmetry.CG.SU2.fuseCGChannel' per channel; see
-- 'Experiments.Symbolic.Reference' for flat-buffer oracles.
--
-- Examples: 'Experiments.SymbolicExamples'.
module Experiments.Symbolic where

import Data.Complex (Complex ((:+)))
import Data.Coerce (coerce)
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))
import Data.Type.Equality ((:~:) (..))
import Data.VectorSpace (InnerSpace ((<.>)), Scalar, VectorSpace ((*^)))
import GHC.TypeLits (CmpNat, KnownNat, Nat, natVal, sameNat, type (*), type (+))
import Control.Arrow.Constrained (($), arr)
import Control.Category.Constrained.Prelude (Category (..))
import Experiments.SU2 (TensorIrrepRepSU2)
import Math.LinearMap.Category
  ( DualVector
  , HilbertSpace
  , (-+$>)
  , fromLinearForm
  , pattern LinearFunction
  , trace
  , type (+>)
  , type (⊗)
  , (⊗)
  )
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.LinearMap.Category.Class (asTensor, fromTensor)
import Math.LinearMap.Coercion ((-+$=>))
import Numeric.LinearAlgebra.Static (C, konst)
import Symmetry.Utils (Append)
import Symmetry.CG.SU2 (fuseCGChannel)
import Symmetry.SU2 (SU2Element, applyWigner)
import TensorNetwork.Categorical
  ( flattenCopyProd
  , flattenTensorProdCopy
  , fuseBond
  , lassocMap
  , mergeCopyAxis
  , mergeCopyAxisTensorLeft
  , rassocMap
  , splitBond
  , swapMap
  , tensorProdLeft
  , (⊗^)
  )

import Prelude hiding (id, (.), ($))

--------------------------------------------------------------------------------
-- Symbolic expressions (SU(2) only)
--------------------------------------------------------------------------------

-- | SU(2) irrep expression: leaf @j@, unfused tensor, or dual.
--
-- @'Tensor@ is recursive so @'Atom@ ⊗ @'Dual ('Atom …)@ is expressible.
-- Historical leaf pairs @'Tensor ('Atom j1) ('Atom j2)@ become @'Tensor ('Atom j1) ('Atom j2)@.
data IrrepExpr
  = Atom Nat
  | Tensor IrrepExpr IrrepExpr
  | Dual IrrepExpr

-- | Formal multiplicity: leaf @m@, unfused product, or dual.
-- Historical @'Prod ('AtomM m) ('AtomM n)@ becomes @'Prod ('AtomM m) ('AtomM n)@.
data MultExpr
  = AtomM Nat
  | Prod MultExpr MultExpr
  | DualM MultExpr

type Sector = (IrrepExpr, MultExpr)
type Rep = [Sector]

--------------------------------------------------------------------------------
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

-- | Singleton for 'IrrepExpr' (bespoke; refines skolem irreps in spine walks).
data SIrrep (e :: IrrepExpr) where
  SAtomI
    :: forall j
     . ( KnownNat j
       , KnownNat (IrrepDim j)
       )
    => SIrrep ('Atom j)
  STensorI
    :: SIrrep e1
    -> SIrrep e2
    -> SIrrep ('Tensor e1 e2)
  SDualI
    :: SIrrep e
    -> SIrrep ('Dual e)

-- | Singleton for 'MultExpr'.
data SMult (μ :: MultExpr) where
  SMultAtom
    :: forall m
     . KnownNat m
    => SMult ('AtomM m)
  SMultProd
    :: SMult μ1
    -> SMult μ2
    -> SMult ('Prod μ1 μ2)
  SMultDual
    :: SMult μ
    -> SMult ('DualM μ)

-- | General spine singleton: one 'SIrrep'/'SMult' pair per sector.
data SRep (rs :: Rep) where
  SRepNil :: SRep '[]
  SRepCons
    :: forall e μ rest
     . SIrrep e
    -> SMult μ
    -> SRep rest
    -> SRep ('(e, μ) ': rest)

-- | Materialize 'SRep' for a statically known spine.
class KnownSymRep (rs :: Rep) where
  symRepSing :: SRep rs

instance KnownSymRep '[] where
  symRepSing = SRepNil

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim j)
  , KnownSymRep rest
  ) =>
  KnownSymRep ('( 'Atom j, 'AtomM m) ': rest)
  where
  symRepSing =
    SRepCons (SAtomI @j) (SMultAtom @m) (symRepSing @rest)

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim j)
  , KnownSymRep rest
  ) =>
  KnownSymRep ('( 'Atom j, 'Prod ('AtomM m) ('AtomM n)) ': rest)
  where
  symRepSing =
    SRepCons
      (SAtomI @j)
      (SMultProd (SMultAtom @m) (SMultAtom @n))
      (symRepSing @rest)

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  , KnownSymRep rest
  ) =>
  KnownSymRep ('( 'Tensor ('Atom j1) ('Atom j2), 'AtomM m) ': rest)
  where
  symRepSing =
    SRepCons
      (STensorI (SAtomI @j1) (SAtomI @j2))
      (SMultAtom @m)
      (symRepSing @rest)

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  , KnownSymRep rest
  ) =>
  KnownSymRep ('( 'Tensor ('Atom j1) ('Atom j2), 'Prod ('AtomM m) ('AtomM n)) ': rest)
  where
  symRepSing =
    SRepCons
      (STensorI (SAtomI @j1) (SAtomI @j2))
      (SMultProd (SMultAtom @m) (SMultAtom @n))
      (symRepSing @rest)

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim j)
  , KnownSymRep rest
  ) =>
  KnownSymRep ('( 'Dual ('Atom j), 'DualM ('AtomM m)) ': rest)
  where
  symRepSing =
    SRepCons
      (SDualI (SAtomI @j))
      (SMultDual (SMultAtom @m))
      (symRepSing @rest)

-- | Atom-only spine (subset of 'KnownSymRep'). Walks use 'symRepSing'.
class KnownSymRep rs => KnownAtomRep (rs :: Rep)

instance KnownAtomRep '[]

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim j)
  , KnownAtomRep rest
  ) =>
  KnownAtomRep ('( 'Atom j, 'AtomM m) ': rest)

-- | Dual-atom-only spine (subset of 'KnownSymRep'). Walks use 'symRepSing'.
class KnownSymRep rs => KnownDualAtomRep (rs :: Rep)

instance KnownDualAtomRep '[]

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim j)
  , KnownDualAtomRep rest
  ) =>
  KnownDualAtomRep ('( 'Dual ('Atom j), 'DualM ('AtomM m)) ': rest)

--------------------------------------------------------------------------------
-- Term-level spine ('RepV') and fusion
--
-- Uniform @RCons@: sector shape lives in the type index @'(e, μ)@, not in a
-- GADT constructor per leaf shape. Old constructor names are pattern synonyms
-- for call sites; discriminating walks match @RCons@ / 'SRep'.
--------------------------------------------------------------------------------

-- | Spine of sectors, indexed by type-level 'Rep'.
data RepV (rs :: Rep) where
  RNil :: RepV '[]
  RCons
    :: forall e μ rest
     . ToVSector e μ
    -> RepV rest
    -> RepV ('(e, μ) ': rest)

pattern RConsAtomAtomM
  :: () => (e ~ 'Atom j, μ ~ 'AtomM m)
  => ToVSector ('Atom j) ('AtomM m)
  -> RepV rest
  -> RepV ('( 'Atom j, 'AtomM m) ': rest)
pattern RConsAtomAtomM v rs = RCons @('Atom j) @('AtomM m) v rs

pattern RConsAtomProd
  :: () => (e ~ 'Atom j, μ ~ 'Prod ('AtomM m) ('AtomM n))
  => ToVSector ('Atom j) ('Prod ('AtomM m) ('AtomM n))
  -> RepV rest
  -> RepV ('( 'Atom j, 'Prod ('AtomM m) ('AtomM n)) ': rest)
pattern RConsAtomProd v rs =
  RCons @('Atom j) @('Prod ('AtomM m) ('AtomM n)) v rs

pattern RConsTensorAtomM
  :: () => (e ~ 'Tensor ('Atom j1) ('Atom j2), μ ~ 'AtomM m)
  => ToVSector ('Tensor ('Atom j1) ('Atom j2)) ('AtomM m)
  -> RepV rest
  -> RepV ('( 'Tensor ('Atom j1) ('Atom j2), 'AtomM m) ': rest)
pattern RConsTensorAtomM v rs =
  RCons @('Tensor ('Atom j1) ('Atom j2)) @('AtomM m) v rs

pattern RConsTensorProd
  :: () => (e ~ 'Tensor ('Atom j1) ('Atom j2), μ ~ 'Prod ('AtomM m) ('AtomM n))
  => ToVSector ('Tensor ('Atom j1) ('Atom j2)) ('Prod ('AtomM m) ('AtomM n))
  -> RepV rest
  -> RepV ('( 'Tensor ('Atom j1) ('Atom j2), 'Prod ('AtomM m) ('AtomM n)) ': rest)
pattern RConsTensorProd v rs =
  RCons @('Tensor ('Atom j1) ('Atom j2)) @('Prod ('AtomM m) ('AtomM n)) v rs

pattern RConsDualAtomDualAtomM
  :: () => (e ~ 'Dual ('Atom j), μ ~ 'DualM ('AtomM m))
  => ToVSector ('Dual ('Atom j)) ('DualM ('AtomM m))
  -> RepV rest
  -> RepV ('( 'Dual ('Atom j), 'DualM ('AtomM m)) ': rest)
pattern RConsDualAtomDualAtomM v rs =
  RCons @('Dual ('Atom j)) @('DualM ('AtomM m)) v rs

pattern RConsTensorAtomDualAtom
  :: () => ( e ~ 'Tensor ('Atom j1) ('Dual ('Atom j2))
     , μ ~ 'Prod ('AtomM m) ('DualM ('AtomM n))
     )
  => ToVSector
       ('Tensor ('Atom j1) ('Dual ('Atom j2)))
       ('Prod ('AtomM m) ('DualM ('AtomM n)))
  -> RepV rest
  -> RepV
       ( '( 'Tensor ('Atom j1) ('Dual ('Atom j2))
          , 'Prod ('AtomM m) ('DualM ('AtomM n))
          )
           ': rest
       )
pattern RConsTensorAtomDualAtom v rs =
  RCons
    @('Tensor ('Atom j1) ('Dual ('Atom j2)))
    @('Prod ('AtomM m) ('DualM ('AtomM n)))
    v
    rs

pattern RConsTensorDualAtomAtom
  :: () => ( e ~ 'Tensor ('Dual ('Atom j1)) ('Atom j2)
     , μ ~ 'Prod ('DualM ('AtomM m)) ('AtomM n)
     )
  => ToVSector
       ('Tensor ('Dual ('Atom j1)) ('Atom j2))
       ('Prod ('DualM ('AtomM m)) ('AtomM n))
  -> RepV rest
  -> RepV
       ( '( 'Tensor ('Dual ('Atom j1)) ('Atom j2)
          , 'Prod ('DualM ('AtomM m)) ('AtomM n)
          )
           ': rest
       )
pattern RConsTensorDualAtomAtom v rs =
  RCons
    @('Tensor ('Dual ('Atom j1)) ('Atom j2))
    @('Prod ('DualM ('AtomM m)) ('AtomM n))
    v
    rs

{-# COMPLETE RNil, RConsAtomAtomM, RConsAtomProd, RConsTensorAtomM,
             RConsTensorProd, RConsDualAtomDualAtomM,
             RConsTensorAtomDualAtom, RConsTensorDualAtomAtom :: RepV #-}

-- | Cons onto a spine (@RCons@; shape from @e@/@μ@).
repCons
  :: forall e μ rest
   . ToVSector e μ
  -> RepV rest
  -> RepV ('(e, μ) ': rest)
repCons = RCons @e @μ

-- | Append two spines (@'Append'@ on keys).
appendRepV
  :: RepV rs1
  -> RepV rs2
  -> RepV (Append rs1 rs2)
appendRepV RNil r2 = r2
appendRepV (RCons v rest) r2 =
  RCons v (appendRepV rest r2)

-- | CG one output channel on irrep legs (@'AtomM'@ copy layout).
fuseOneChannelAtomM
  :: forall j1 j2 j m
   . ( KnownNat j1
     , KnownNat j2
     , KnownNat j
     , KnownNat m
     , KnownNat (IrrepDim j1)
     , KnownNat (IrrepDim j2)
     , KnownNat (IrrepDim j)
     )
  => ToVSector ('Tensor ('Atom j1) ('Atom j2)) ('AtomM m)
  -> ToVSector ('Atom j) ('AtomM m)
fuseOneChannelAtomM sec =
  ((id ⊗^ fuseCGChannel @j1 @j2 @j) . rassocMap) $ sec

-- | CG one output channel on irrep legs (@'Prod'@ copy layout).
fuseOneChannelProd
  :: forall j1 j2 j m n
   . ( KnownNat j1
     , KnownNat j2
     , KnownNat j
     , KnownNat m
     , KnownNat n
     , KnownNat (IrrepDim j1)
     , KnownNat (IrrepDim j2)
     , KnownNat (IrrepDim j)
     , KnownNat (m * n)
     )
  => ToVSector ('Tensor ('Atom j1) ('Atom j2)) ('Prod ('AtomM m) ('AtomM n))
  -> ToVSector ('Atom j) ('Prod ('AtomM m) ('AtomM n))
fuseOneChannelProd sec =
  ( (id ⊗^ fuseCGChannel @j1 @j2 @j)
      . (splitBond @m @n ⊗^ id)
      . arr (LinearFunction flattenTensorProdCopy)
  )
    $ sec

-- | Walk @'TensorIrrepRepSU2'@ channels, building a tagged atom spine.
class FuseTensorSpine (j1 :: Nat) (j2 :: Nat) (μ :: MultExpr) (cg :: [(Nat, Nat)]) where
  fuseTensorSpine
    :: ToVSector ('Tensor ('Atom j1) ('Atom j2)) μ
    -> RepV (TagMult μ (AtomsFromCG cg))

instance FuseTensorSpine j1 j2 μ '[] where
  fuseTensorSpine _ = RNil

instance
  ( FuseTensorSpine j1 j2 ('AtomM m) rest
  , KnownNat j
  , KnownNat j1
  , KnownNat j2
  , KnownNat m
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  , KnownNat (IrrepDim j)
  ) =>
  FuseTensorSpine j1 j2 ('AtomM m) ('(j, mOut) ': rest)
  where
  fuseTensorSpine v =
    repCons @('Atom j) @('AtomM m)
      (fuseOneChannelAtomM @j1 @j2 @j @m v)
      (fuseTensorSpine @j1 @j2 @('AtomM m) @rest v)

instance
  ( FuseTensorSpine j1 j2 ('Prod ('AtomM m) ('AtomM n)) rest
  , KnownNat j
  , KnownNat j1
  , KnownNat j2
  , KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  , KnownNat (IrrepDim j)
  , KnownNat (m * n)
  ) =>
  FuseTensorSpine j1 j2 ('Prod ('AtomM m) ('AtomM n)) ('(j, mOut) ': rest)
  where
  fuseTensorSpine v =
    repCons @('Atom j) @('Prod ('AtomM m) ('AtomM n))
      (fuseOneChannelProd @j1 @j2 @j @m @n v)
      (fuseTensorSpine @j1 @j2 @('Prod ('AtomM m) ('AtomM n)) @rest v)

-- | CG-fuse one sector to a (possibly longer) atom spine.
fuseOneSectorAtomAtomM
  :: forall j m
   . ToVSector ('Atom j) ('AtomM m)
  -> RepV '[ '( 'Atom j, 'AtomM m)]
fuseOneSectorAtomAtomM v = RConsAtomAtomM v RNil

fuseOneSectorAtomProd
  :: forall j m n
   . ToVSector ('Atom j) ('Prod ('AtomM m) ('AtomM n))
  -> RepV '[ '( 'Atom j, 'Prod ('AtomM m) ('AtomM n))]
fuseOneSectorAtomProd v = RConsAtomProd v RNil

fuseOneSectorTensorAtomM
  :: forall j1 j2 m
   . ( KnownNat j1
     , KnownNat j2
     , KnownNat m
     , FuseTensorSpine j1 j2 ('AtomM m) (TensorIrrepRepSU2 j1 j2)
     )
  => ToVSector ('Tensor ('Atom j1) ('Atom j2)) ('AtomM m)
  -> RepV (FuseSector '( 'Tensor ('Atom j1) ('Atom j2), 'AtomM m))
fuseOneSectorTensorAtomM =
  fuseTensorSpine @j1 @j2 @('AtomM m) @(TensorIrrepRepSU2 j1 j2)

fuseOneSectorTensorProd
  :: forall j1 j2 m n
   . ( KnownNat j1
     , KnownNat j2
     , KnownNat m
     , KnownNat n
     , FuseTensorSpine j1 j2 ('Prod ('AtomM m) ('AtomM n)) (TensorIrrepRepSU2 j1 j2)
     )
  => ToVSector ('Tensor ('Atom j1) ('Atom j2)) ('Prod ('AtomM m) ('AtomM n))
  -> RepV (FuseSector '( 'Tensor ('Atom j1) ('Atom j2), 'Prod ('AtomM m) ('AtomM n)))
fuseOneSectorTensorProd =
  fuseTensorSpine @j1 @j2 @('Prod ('AtomM m) ('AtomM n)) @(TensorIrrepRepSU2 j1 j2)

--------------------------------------------------------------------------------
-- Undual (Fuse identification): DualVector → primal atom payload
--
-- Type-level 'UndualIrrep' / 'UndualMult' strip Dual labels. Term-level undual
-- inverts 'dualAtomAtomM' by 'asTensor' + Hilbert coerce on each @C n@ factor
-- (@DualVector (u ⊗ v) = u +> DualVector v@). SU(2) Condon–Shortley phases are
-- not applied here yet; needed for fused-cup coherence on non-trivial irreps.
--------------------------------------------------------------------------------

-- | Inverse of 'dualAtomAtomM': @DualVector (C m ⊗ C (j+1)) → C m ⊗ C (j+1)@.
--
-- @DualVector (u ⊗ v) = u +> DualVector v@. With Hilbert @DualVector (C n) ~ C n@,
-- 'asTensor' recovers @DualVector (C m) ⊗ DualVector (C (j+1))@, then coerce
-- both factors. Avoids @toLinearForm@ on nested tensor duals (COrphans bug).
undualAtomAtomM
  :: forall j m
   . ( KnownNat j
     , KnownNat m
     , KnownNat (IrrepDim j)
     , HilbertSpace (C m)
     , HilbertSpace (C (IrrepDim j))
     )
  => ToVSector ('Dual ('Atom j)) ('DualM ('AtomM m))
  -> ToVSector ('Atom j) ('AtomM m)
undualAtomAtomM φ =
  let tDual =
        asTensor -+$=> φ
          :: DualVector (C m) ⊗ DualVector (C (IrrepDim j))
   in ( arr (LinearFunction (coerce :: DualVector (C m) -> C m))
          ⊗^ arr (LinearFunction (coerce :: DualVector (C (IrrepDim j)) -> C (IrrepDim j)))
      )
        $ tDual

-- | Sector algebra for CG fuse (spine walk is a plain fold over 'FuseRawSpine').
class FuseOneSector (e :: IrrepExpr) (μ :: MultExpr) where
  fuseOneSector :: ToVSector e μ -> RepV (FuseSector '(e, μ))

instance FuseOneSector ('Atom j) ('AtomM m) where
  fuseOneSector = fuseOneSectorAtomAtomM

instance FuseOneSector ('Atom j) ('Prod ('AtomM m) ('AtomM n)) where
  fuseOneSector = fuseOneSectorAtomProd

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m
  , FuseTensorSpine j1 j2 ('AtomM m) (TensorIrrepRepSU2 j1 j2)
  ) =>
  FuseOneSector ('Tensor ('Atom j1) ('Atom j2)) ('AtomM m)
  where
  fuseOneSector = fuseOneSectorTensorAtomM

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m
  , KnownNat n
  , FuseTensorSpine j1 j2 ('Prod ('AtomM m) ('AtomM n)) (TensorIrrepRepSU2 j1 j2)
  ) =>
  FuseOneSector ('Tensor ('Atom j1) ('Atom j2)) ('Prod ('AtomM m) ('AtomM n))
  where
  fuseOneSector = fuseOneSectorTensorProd

-- | Dual leaf: undual payload, land on @'Atom j@ / @'AtomM m@.
instance
  ( KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim j)
  , HilbertSpace (C m)
  , HilbertSpace (C (IrrepDim j))
  ) =>
  FuseOneSector ('Dual ('Atom j)) ('DualM ('AtomM m))
  where
  fuseOneSector φ =
    RConsAtomAtomM (undualAtomAtomM @j @m φ) RNil

-- | @Atom ⊗ Dual Atom@: undual the right factor, then CG as primal tensor.
instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  , HilbertSpace (C n)
  , HilbertSpace (C (IrrepDim j2))
  , FuseTensorSpine j1 j2 ('Prod ('AtomM m) ('AtomM n)) (TensorIrrepRepSU2 j1 j2)
  ) =>
  FuseOneSector
    ('Tensor ('Atom j1) ('Dual ('Atom j2)))
    ('Prod ('AtomM m) ('DualM ('AtomM n)))
  where
  fuseOneSector t =
    let undualed =
          (id ⊗^ arr (LinearFunction (undualAtomAtomM @j2 @n))) $ t
            :: ToVSector
                 ('Tensor ('Atom j1) ('Atom j2))
                 ('Prod ('AtomM m) ('AtomM n))
     in fuseOneSectorTensorProd @j1 @j2 @m @n undualed

-- | @Dual Atom ⊗ Atom@: undual the left factor, then CG as primal tensor.
instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  , HilbertSpace (C m)
  , HilbertSpace (C (IrrepDim j1))
  , FuseTensorSpine j1 j2 ('Prod ('AtomM m) ('AtomM n)) (TensorIrrepRepSU2 j1 j2)
  ) =>
  FuseOneSector
    ('Tensor ('Dual ('Atom j1)) ('Atom j2))
    ('Prod ('DualM ('AtomM m)) ('AtomM n))
  where
  fuseOneSector t =
    let undualed =
          (arr (LinearFunction (undualAtomAtomM @j1 @m)) ⊗^ id) $ t
            :: ToVSector
                 ('Tensor ('Atom j1) ('Atom j2))
                 ('Prod ('AtomM m) ('AtomM n))
     in fuseOneSectorTensorProd @j1 @j2 @m @n undualed

-- | Insert one sector into a coalesced spine (sort + merge on equal keys).
class InsertSpine (e :: IrrepExpr) (μ :: MultExpr) (rs :: Rep) where
  insertSpine
    :: ToVSector e μ
    -> RepV rs
    -> RepV (InsertSector e μ rs)

instance InsertSpine e μ '[] where
  insertSpine sv RNil = repCons @e @μ sv RNil

instance
  ( CmpIrrep e ('Atom j) ~ ord
  , InsertCompared ord e μ ('Atom j) ('AtomM m) rest
  ) =>
  InsertSpine e μ ('( 'Atom j, 'AtomM m) ': rest)
  where
  insertSpine sv (RConsAtomAtomM sv2 restR) =
    insertCompared @ord @e @μ @('Atom j) @('AtomM m) sv sv2 restR

instance
  ( CmpIrrep e ('Atom j) ~ ord
  , InsertCompared ord e μ ('Atom j) ('Prod ('AtomM m) ('AtomM n)) rest
  ) =>
  InsertSpine e μ ('( 'Atom j, 'Prod ('AtomM m) ('AtomM n)) ': rest)
  where
  insertSpine sv (RConsAtomProd sv2 restR) =
    insertCompared @ord @e @μ @('Atom j) @('Prod ('AtomM m) ('AtomM n)) sv sv2 restR

instance
  ( CmpIrrep e ('Tensor ('Atom j1) ('Atom j2)) ~ ord
  , InsertCompared ord e μ ('Tensor ('Atom j1) ('Atom j2)) ('AtomM m) rest
  ) =>
  InsertSpine e μ ('( 'Tensor ('Atom j1) ('Atom j2), 'AtomM m) ': rest)
  where
  insertSpine sv (RConsTensorAtomM sv2 restR) =
    insertCompared @ord @e @μ @('Tensor ('Atom j1) ('Atom j2)) @('AtomM m) sv sv2 restR

instance
  ( CmpIrrep e ('Tensor ('Atom j1) ('Atom j2)) ~ ord
  , InsertCompared ord e μ ('Tensor ('Atom j1) ('Atom j2)) ('Prod ('AtomM m) ('AtomM n)) rest
  ) =>
  InsertSpine e μ ('( 'Tensor ('Atom j1) ('Atom j2), 'Prod ('AtomM m) ('AtomM n)) ': rest)
  where
  insertSpine sv (RConsTensorProd sv2 restR) =
    insertCompared @ord @e @μ @('Tensor ('Atom j1) ('Atom j2)) @('Prod ('AtomM m) ('AtomM n)) sv sv2 restR

instance
  ( CmpIrrep e ('Dual ('Atom j)) ~ ord
  , InsertCompared ord e μ ('Dual ('Atom j)) ('DualM ('AtomM m)) rest
  ) =>
  InsertSpine e μ ('( 'Dual ('Atom j), 'DualM ('AtomM m)) ': rest)
  where
  insertSpine sv (RConsDualAtomDualAtomM sv2 restR) =
    insertCompared @ord @e @μ @('Dual ('Atom j)) @('DualM ('AtomM m)) sv sv2 restR

instance
  ( CmpIrrep e ('Tensor ('Atom j1) ('Dual ('Atom j2))) ~ ord
  , InsertCompared
      ord
      e
      μ
      ('Tensor ('Atom j1) ('Dual ('Atom j2)))
      ('Prod ('AtomM m) ('DualM ('AtomM n)))
      rest
  ) =>
  InsertSpine
    e
    μ
    ( '( 'Tensor ('Atom j1) ('Dual ('Atom j2))
       , 'Prod ('AtomM m) ('DualM ('AtomM n))
       )
        ': rest
    )
  where
  insertSpine sv (RConsTensorAtomDualAtom sv2 restR) =
    insertCompared
      @ord
      @e
      @μ
      @('Tensor ('Atom j1) ('Dual ('Atom j2)))
      @('Prod ('AtomM m) ('DualM ('AtomM n)))
      sv
      sv2
      restR

instance
  ( CmpIrrep e ('Tensor ('Dual ('Atom j1)) ('Atom j2)) ~ ord
  , InsertCompared
      ord
      e
      μ
      ('Tensor ('Dual ('Atom j1)) ('Atom j2))
      ('Prod ('DualM ('AtomM m)) ('AtomM n))
      rest
  ) =>
  InsertSpine
    e
    μ
    ( '( 'Tensor ('Dual ('Atom j1)) ('Atom j2)
       , 'Prod ('DualM ('AtomM m)) ('AtomM n)
       )
        ': rest
    )
  where
  insertSpine sv (RConsTensorDualAtomAtom sv2 restR) =
    insertCompared
      @ord
      @e
      @μ
      @('Tensor ('Dual ('Atom j1)) ('Atom j2))
      @('Prod ('DualM ('AtomM m)) ('AtomM n))
      sv
      sv2
      restR

-- | Compare incoming sector @e@ against spine head @e2@ (@ord ~ CmpIrrep e e2@).
class InsertCompared
  (ord :: Ordering)
  (e :: IrrepExpr) (μ :: MultExpr)
  (e2 :: IrrepExpr) (μ2 :: MultExpr)
  (rest :: Rep)
 where
  insertCompared
    :: ToVSector e μ
    -> ToVSector e2 μ2
    -> RepV rest
    -> RepV (InsertSectorOrd ord e μ e2 μ2 rest)

-- | Direct-sum same-'IrrepExpr' sectors along the copy axis (coalesce).
-- Output multiplicity is always @'AtomM@.
class MergeSector (e :: IrrepExpr) (μ1 :: MultExpr) (μ2 :: MultExpr) (μOut :: MultExpr) where
  mergeSector
    :: ToVSector e μ1
    -> ToVSector e μ2
    -> ToVSector e μOut

instance
  ( KnownNat j
  , KnownNat m1
  , KnownNat m2
  , KnownNat mOut
  , mOut ~ m1 + m2
  , KnownNat (IrrepDim j)
  ) =>
  MergeSector ('Atom j) ('AtomM m1) ('AtomM m2) ('AtomM mOut)
  where
  mergeSector v1 v2 =
    mergeCopyAxis @m1 @m2 @(IrrepDim j) v1 v2

instance
  ( KnownNat j
  , KnownNat m1
  , KnownNat n1
  , KnownNat m2
  , KnownNat n2
  , KnownNat ma
  , KnownNat mb
  , KnownNat mOut
  , ma ~ m1 * n1
  , mb ~ m2 * n2
  , mOut ~ ma + mb
  , KnownNat (IrrepDim j)
  ) =>
  MergeSector ('Atom j) ('Prod ('AtomM m1) ('AtomM n1)) ('Prod ('AtomM m2) ('AtomM n2)) ('AtomM mOut)
  where
  mergeSector v1 v2 =
    mergeCopyAxis @ma @mb @(IrrepDim j)
      (flattenCopyProd @m1 @n1 @(IrrepDim j) v1)
      (flattenCopyProd @m2 @n2 @(IrrepDim j) v2)

instance
  ( KnownNat j
  , KnownNat m1
  , KnownNat m2
  , KnownNat n2
  , KnownNat mb
  , KnownNat mOut
  , mb ~ m2 * n2
  , mOut ~ m1 + mb
  , KnownNat (IrrepDim j)
  ) =>
  MergeSector ('Atom j) ('AtomM m1) ('Prod ('AtomM m2) ('AtomM n2)) ('AtomM mOut)
  where
  mergeSector v1 v2 =
    mergeCopyAxis @m1 @mb @(IrrepDim j) v1
      (flattenCopyProd @m2 @n2 @(IrrepDim j) v2)

instance
  ( KnownNat j
  , KnownNat m1
  , KnownNat n1
  , KnownNat m2
  , KnownNat ma
  , KnownNat mOut
  , ma ~ m1 * n1
  , mOut ~ ma + m2
  , KnownNat (IrrepDim j)
  ) =>
  MergeSector ('Atom j) ('Prod ('AtomM m1) ('AtomM n1)) ('AtomM m2) ('AtomM mOut)
  where
  mergeSector v1 v2 =
    mergeCopyAxis @ma @m2 @(IrrepDim j)
      (flattenCopyProd @m1 @n1 @(IrrepDim j) v1)
      v2

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m1
  , KnownNat m2
  , KnownNat mOut
  , mOut ~ m1 + m2
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  ) =>
  MergeSector ('Tensor ('Atom j1) ('Atom j2)) ('AtomM m1) ('AtomM m2) ('AtomM mOut)
  where
  mergeSector v1 v2 =
    mergeCopyAxisTensorLeft @m1 @m2 @(IrrepDim j1) @(IrrepDim j2) v1 v2

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m1
  , KnownNat n1
  , KnownNat m2
  , KnownNat n2
  , KnownNat ma
  , KnownNat mb
  , KnownNat mOut
  , ma ~ m1 * n1
  , mb ~ m2 * n2
  , mOut ~ ma + mb
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  ) =>
  MergeSector ('Tensor ('Atom j1) ('Atom j2)) ('Prod ('AtomM m1) ('AtomM n1)) ('Prod ('AtomM m2) ('AtomM n2)) ('AtomM mOut)
  where
  mergeSector v1 v2 =
    mergeCopyAxisTensorLeft @ma @mb @(IrrepDim j1) @(IrrepDim j2)
      (tensorProdLeft (flattenTensorProdCopy @m1 @n1 @(IrrepDim j1) @(IrrepDim j2) v1))
      (tensorProdLeft (flattenTensorProdCopy @m2 @n2 @(IrrepDim j1) @(IrrepDim j2) v2))

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m1
  , KnownNat m2
  , KnownNat n2
  , KnownNat mb
  , KnownNat mOut
  , mb ~ m2 * n2
  , mOut ~ m1 + mb
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  ) =>
  MergeSector ('Tensor ('Atom j1) ('Atom j2)) ('AtomM m1) ('Prod ('AtomM m2) ('AtomM n2)) ('AtomM mOut)
  where
  mergeSector v1 v2 =
    mergeCopyAxisTensorLeft @m1 @mb @(IrrepDim j1) @(IrrepDim j2) v1
      (tensorProdLeft (flattenTensorProdCopy @m2 @n2 @(IrrepDim j1) @(IrrepDim j2) v2))

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m1
  , KnownNat n1
  , KnownNat m2
  , KnownNat ma
  , KnownNat mOut
  , ma ~ m1 * n1
  , mOut ~ ma + m2
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  ) =>
  MergeSector ('Tensor ('Atom j1) ('Atom j2)) ('Prod ('AtomM m1) ('AtomM n1)) ('AtomM m2) ('AtomM mOut)
  where
  mergeSector v1 v2 =
    mergeCopyAxisTensorLeft @ma @m2 @(IrrepDim j1) @(IrrepDim j2)
      (tensorProdLeft (flattenTensorProdCopy @m1 @n1 @(IrrepDim j1) @(IrrepDim j2) v1))
      v2

instance
  ( j ~ k
  , AddMult μ μ2 ~ μOut
  , MergeSector ('Atom j) μ μ2 μOut
  ) =>
  InsertCompared 'EQ ('Atom j) μ ('Atom k) μ2 rest
  where
  insertCompared sv sv2 restR =
    RConsAtomAtomM (mergeSector @('Atom j) @μ @μ2 @μOut sv sv2) restR

instance
  InsertCompared 'LT ('Atom j) μ ('Atom k) μ2 rest
  where
  insertCompared sv sv2 restR =
    repCons @('Atom j) @μ sv (repCons @('Atom k) @μ2 sv2 restR)

instance
  ( InsertSpine ('Atom j) μ rest
  ) =>
  InsertCompared 'GT ('Atom j) μ ('Atom k) μ2 rest
  where
  insertCompared sv sv2 restR =
    repCons @('Atom k) @μ2 sv2 (insertSpine @('Atom j) @μ sv restR)

instance
  InsertCompared 'LT ('Atom j) μ ('Tensor ('Atom k1) ('Atom k2)) μ2 rest
  where
  insertCompared sv sv2 restR =
    repCons @('Atom j) @μ sv (repCons @('Tensor ('Atom k1) ('Atom k2)) @μ2 sv2 restR)

instance
  ( InsertSpine ('Tensor ('Atom j1) ('Atom j2)) μ rest
  ) =>
  InsertCompared 'GT ('Tensor ('Atom j1) ('Atom j2)) μ ('Atom k) μ2 rest
  where
  insertCompared sv sv2 restR =
    repCons @('Atom k) @μ2 sv2 (insertSpine @('Tensor ('Atom j1) ('Atom j2)) @μ sv restR)

instance
  InsertCompared 'LT ('Tensor ('Atom j1) ('Atom j2)) μ ('Tensor ('Atom k1) ('Atom k2)) μ2 rest
  where
  insertCompared sv sv2 restR =
    repCons @('Tensor ('Atom j1) ('Atom j2)) @μ
      sv
      (repCons @('Tensor ('Atom k1) ('Atom k2)) @μ2 sv2 restR)

instance
  ( InsertSpine ('Tensor ('Atom j1) ('Atom j2)) μ rest
  ) =>
  InsertCompared 'GT ('Tensor ('Atom j1) ('Atom j2)) μ ('Tensor ('Atom k1) ('Atom k2)) μ2 rest
  where
  insertCompared sv sv2 restR =
    repCons @('Tensor ('Atom k1) ('Atom k2)) @μ2
      sv2
      (insertSpine @('Tensor ('Atom j1) ('Atom j2)) @μ sv restR)

instance
  ( j1 ~ k1
  , j2 ~ k2
  , AddMult μ μ2 ~ μOut
  , MergeSector ('Tensor ('Atom j1) ('Atom j2)) μ μ2 μOut
  ) =>
  InsertCompared 'EQ ('Tensor ('Atom j1) ('Atom j2)) μ ('Tensor ('Atom k1) ('Atom k2)) μ2 rest
  where
  insertCompared sv sv2 restR =
    RConsTensorAtomM
      (mergeSector @('Tensor ('Atom j1) ('Atom j2)) @μ @μ2 @μOut sv sv2)
      restR

-- Dual leaf vs Atom / Dual (sort order: Atom < Tensor < Dual).
instance
  InsertCompared 'LT ('Atom j) μ ('Dual ('Atom k)) μ2 rest
  where
  insertCompared sv sv2 restR =
    repCons @('Atom j) @μ sv (repCons @('Dual ('Atom k)) @μ2 sv2 restR)

instance
  ( InsertSpine ('Dual ('Atom j)) μ rest
  ) =>
  InsertCompared 'GT ('Dual ('Atom j)) μ ('Atom k) μ2 rest
  where
  insertCompared sv sv2 restR =
    repCons @('Atom k) @μ2 sv2 (insertSpine @('Dual ('Atom j)) @μ sv restR)

instance
  InsertCompared 'LT ('Tensor ('Atom j1) ('Atom j2)) μ ('Dual ('Atom k)) μ2 rest
  where
  insertCompared sv sv2 restR =
    repCons @('Tensor ('Atom j1) ('Atom j2)) @μ
      sv
      (repCons @('Dual ('Atom k)) @μ2 sv2 restR)

instance
  ( InsertSpine ('Dual ('Atom j)) μ rest
  ) =>
  InsertCompared 'GT ('Dual ('Atom j)) μ ('Tensor ('Atom k1) ('Atom k2)) μ2 rest
  where
  insertCompared sv sv2 restR =
    repCons @('Tensor ('Atom k1) ('Atom k2)) @μ2
      sv2
      (insertSpine @('Dual ('Atom j)) @μ sv restR)

instance
  InsertCompared 'LT ('Dual ('Atom j)) μ ('Dual ('Atom k)) μ2 rest
  where
  insertCompared sv sv2 restR =
    repCons @('Dual ('Atom j)) @μ
      sv
      (repCons @('Dual ('Atom k)) @μ2 sv2 restR)

instance
  ( InsertSpine ('Dual ('Atom j)) μ rest
  ) =>
  InsertCompared 'GT ('Dual ('Atom j)) μ ('Dual ('Atom k)) μ2 rest
  where
  insertCompared sv sv2 restR =
    repCons @('Dual ('Atom k)) @μ2
      sv2
      (insertSpine @('Dual ('Atom j)) @μ sv restR)

-- EQ Dual↔Dual merge omitted: AddMult → 'AtomM conflicts with Dual ToVSector
-- expecting 'DualM. Coalesce of equal Dual keys is intentionally unsupported until
-- Dual copy-merge is designed.

-- | Constraints for CG-fusing every sector (@FuseOneSector@ per head).
-- Plain fold matches @RCons @e @μ@; no spine walk class.
type family FuseRawSpine (rs :: Rep) :: Constraint where
  FuseRawSpine '[] = ()
  FuseRawSpine ('(e, μ) ': rest) =
    ( FuseOneSector e μ
    , FuseRawSpine rest
    )

-- | CG-fuse every sector in a spine, append (no coalesce).
fuseRaw
  :: FuseRawSpine rs
  => RepV rs
  -> RepV (FuseRepRaw rs)
fuseRaw RNil = RNil
fuseRaw (RCons @e @μ sv rs) =
  appendRepV (fuseOneSector @e @μ sv) (fuseRaw rs)

-- | Constraints for coalescing: 'InsertSpine' into the coalesced tail.
type family CoalesceSpine (rs :: Rep) :: Constraint where
  CoalesceSpine '[] = ()
  CoalesceSpine ('(e, μ) ': rest) =
    ( InsertSpine e μ (Coalesce rest)
    , CoalesceSpine rest
    )

-- | Sort + merge equal @'IrrepExpr'@ keys on a spine ('SRep' fold).
coalesce
  :: forall rs
   . ( KnownSymRep rs
     , CoalesceSpine rs
     )
  => RepV rs
  -> RepV (Coalesce rs)
coalesce = go (symRepSing @rs)
  where
    go :: forall rs'. CoalesceSpine rs' => SRep rs' -> RepV rs' -> RepV (Coalesce rs')
    go SRepNil RNil = RNil
    go (SRepCons @e @μ _ _ rest) (RCons sv rs) =
      insertSpine @e @μ sv (go rest rs)

-- | CG fuse every sector, append, coalesce.
fuse :: ( FuseRawSpine rs
     , KnownSymRep (FuseRepRaw rs)
     , CoalesceSpine (FuseRepRaw rs)
     )
  => RepV rs
  -> RepV (Fuse rs)
fuse rv =
  coalesce (fuseRaw rv)

-- | CG fuse a distributed tensor rep (@'Tensor'@).
fuseTensor
  :: ( FuseRawSpine (Tensor r s)
     , KnownSymRep (FuseRepRaw (Tensor r s))
     , CoalesceSpine (FuseRepRaw (Tensor r s))
     )
  => RepV (Tensor r s)
  -> RepV (Fuse (Tensor r s))
fuseTensor = fuse

-- | Build unfused @'Tensor'@ from two atom sectors (pair layout).
tensorAtoms
  :: forall j1 m1 j2 m2
   . ( KnownNat j1
     , KnownNat m1
     , KnownNat j2
     , KnownNat m2
     , KnownNat (IrrepDim j1)
     , KnownNat (IrrepDim j2)
     )
  => C m1 ⊗ C (IrrepDim j1)
  -> C m2 ⊗ C (IrrepDim j2)
  -> RepV
       ( Tensor
           '[ '( 'Atom j1, 'AtomM m1)]
           '[ '( 'Atom j2, 'AtomM m2)]
       )
tensorAtoms s1 s2 =
  tensorAtom
    (RConsAtomAtomM s1 RNil)
    (RConsAtomAtomM s2 RNil)

-- | Pair one left atom sector with a right atom spine ('SRep' / 'KnownAtomRep').
tensorOneAtom
  :: forall j m q
   . ( KnownNat j
     , KnownNat m
     , KnownNat (IrrepDim j)
     , KnownAtomRep q
     )
  => ToVSector ('Atom j) ('AtomM m)
  -> RepV q
  -> RepV (TensorOne '( 'Atom j, 'AtomM m) q)
tensorOneAtom s1 = go (symRepSing @q)
  where
    go :: forall q'. SRep q' -> RepV q' -> RepV (TensorOne '( 'Atom j, 'AtomM m) q')
    go SRepNil RNil = RNil
    go (SRepCons (SAtomI @j2) (SMultAtom @n) rest) (RCons s2 qRest) =
      RCons (s1 ⊗ s2) (go rest qRest)
    go _ _ = error "tensorOneAtom: expected atom spine"

-- | Atom×atom Cartesian tensor via 'SRep'.
tensorAtom
  :: forall r q
   . ( KnownAtomRep r
     , KnownAtomRep q
     )
  => RepV r
  -> RepV q
  -> RepV (Tensor r q)
tensorAtom r q = go (symRepSing @r) r
  where
    go :: forall r'. SRep r' -> RepV r' -> RepV (Tensor r' q)
    go SRepNil RNil = RNil
    go (SRepCons (SAtomI @j) (SMultAtom @m) rest) (RCons s1 rRest) =
      appendRepV (tensorOneAtom @j @m s1 q) (go rest rRest)
    go _ _ = error "tensorAtom: expected atom spine"

-- | Pair one left dual-atom sector with a right atom spine.
tensorOneDualAtom
  :: forall j m q
   . ( KnownNat j
     , KnownNat m
     , KnownNat (IrrepDim j)
     , KnownAtomRep q
     )
  => ToVSector ('Dual ('Atom j)) ('DualM ('AtomM m))
  -> RepV q
  -> RepV (TensorOne '( 'Dual ('Atom j), 'DualM ('AtomM m)) q)
tensorOneDualAtom s1 = go (symRepSing @q)
  where
    go
      :: forall q'
       . SRep q'
      -> RepV q'
      -> RepV (TensorOne '( 'Dual ('Atom j), 'DualM ('AtomM m)) q')
    go SRepNil RNil = RNil
    go (SRepCons SAtomI SMultAtom rest) (RCons s2 qRest) =
      RCons (s1 ⊗ s2) (go rest qRest)
    go _ _ = error "tensorOneDualAtom: expected atom spine"

-- | Dual-atom × atom Cartesian tensor via 'SRep'.
tensorDualAtom
  :: forall r q
   . ( KnownDualAtomRep r
     , KnownAtomRep q
     )
  => RepV r
  -> RepV q
  -> RepV (Tensor r q)
tensorDualAtom r q = go (symRepSing @r) r
  where
    go :: forall r'. SRep r' -> RepV r' -> RepV (Tensor r' q)
    go SRepNil RNil = RNil
    go (SRepCons (SDualI (SAtomI @j)) (SMultDual (SMultAtom @m)) rest) (RCons s1 rRest) =
      appendRepV (tensorOneDualAtom @j @m s1 q) (go rest rRest)
    go _ _ = error "tensorDualAtom: expected dual-atom spine"

-- | Pair one left atom sector with a right dual-atom spine.
tensorOneAtomDual
  :: forall j m q
   . ( KnownNat j
     , KnownNat m
     , KnownNat (IrrepDim j)
     , KnownDualAtomRep q
     )
  => ToVSector ('Atom j) ('AtomM m)
  -> RepV q
  -> RepV (TensorOne '( 'Atom j, 'AtomM m) q)
tensorOneAtomDual s1 = go (symRepSing @q)
  where
    go
      :: forall q'
       . SRep q'
      -> RepV q'
      -> RepV (TensorOne '( 'Atom j, 'AtomM m) q')
    go SRepNil RNil = RNil
    go (SRepCons (SDualI SAtomI) (SMultDual SMultAtom) rest) (RCons s2 qRest) =
      RCons (s1 ⊗ s2) (go rest qRest)
    go _ _ = error "tensorOneAtomDual: expected dual-atom spine"

-- | Atom × dual-atom Cartesian tensor.
tensorAtomDual
  :: forall r q
   . ( KnownAtomRep r
     , KnownDualAtomRep q
     )
  => RepV r
  -> RepV q
  -> RepV (Tensor r q)
tensorAtomDual r q = go (symRepSing @r) r
  where
    go :: forall r'. SRep r' -> RepV r' -> RepV (Tensor r' q)
    go SRepNil RNil = RNil
    go (SRepCons (SAtomI @j) (SMultAtom @m) rest) (RCons s1 rRest) =
      appendRepV (tensorOneAtomDual @j @m s1 q) (go rest rRest)
    go _ _ = error "tensorAtomDual: expected atom spine"

-- | Leaf×leaf atom×atom tensor ('Tensor' type family). Dual sides use
-- 'tensorDualAtom' / 'tensorAtomDual' explicitly (no walk class).
tensor
  :: ( KnownAtomRep r
     , KnownAtomRep q
     )
  => RepV r
  -> RepV q
  -> RepV (Tensor r q)
tensor = tensorAtom

--------------------------------------------------------------------------------
-- SU(2) group action (Wigner on irrep legs)
--
-- @g ↦ (RepV rs → RepV rs)@: identity on copy axes, @D^{j/2}(g)@ on each
-- irrep factor (Kronecker on unfused @'Tensor@). Dual / mixed dual tensors
-- are not wired yet.
--------------------------------------------------------------------------------

-- | Wigner @D^{j/2}(g)@ as a typed morphism on the CG magnetic basis.
wignerD
  :: forall j
   . KnownNat j
  => SU2Element
  -> C (IrrepDim j) +> C (IrrepDim j)
wignerD g =
  arr $
    LinearFunction $
      applyWigner (fromIntegral (natVal (Proxy @j))) g

-- | Sector morphism: @id@ on multiplicity, Wigner on irrep factor(s).
sectorMap
  :: SIrrep e
  -> SMult μ
  -> SU2Element
  -> ToVSector e μ +> ToVSector e μ
sectorMap (SAtomI @j) SMultAtom g =
  id ⊗^ wignerD @j g
sectorMap (SAtomI @j) (SMultProd SMultAtom SMultAtom) g =
  id ⊗^ wignerD @j g
sectorMap (STensorI (SAtomI @j1) (SAtomI @j2)) SMultAtom g =
  (id ⊗^ wignerD @j1 g) ⊗^ wignerD @j2 g
sectorMap
  (STensorI (SAtomI @j1) (SAtomI @j2))
  (SMultProd SMultAtom SMultAtom)
  g =
  (id ⊗^ wignerD @j1 g) ⊗^ (id ⊗^ wignerD @j2 g)
sectorMap _ _ _ =
  error "Experiments.Symbolic.sectorMap: dual / unsupported sector (blocker)"

-- | Apply 'sectorMap' to a sector payload.
actSector
  :: SIrrep e
  -> SMult μ
  -> SU2Element
  -> ToVSector e μ
  -> ToVSector e μ
actSector (SAtomI @j) SMultAtom g v =
  (id ⊗^ wignerD @j g) $ v
actSector (SAtomI @j) (SMultProd SMultAtom SMultAtom) g v =
  (id ⊗^ wignerD @j g) $ v
actSector (STensorI (SAtomI @j1) (SAtomI @j2)) SMultAtom g v =
  ((id ⊗^ wignerD @j1 g) ⊗^ wignerD @j2 g) $ v
actSector
  (STensorI (SAtomI @j1) (SAtomI @j2))
  (SMultProd SMultAtom SMultAtom)
  g
  v =
  ((id ⊗^ wignerD @j1 g) ⊗^ (id ⊗^ wignerD @j2 g)) $ v
actSector _ _ _ _ =
  error "Experiments.Symbolic.actSector: dual / unsupported sector (blocker)"

-- | Group action on a spine: @SU2Element → (RepV rs → RepV rs)@.
actRep
  :: forall rs
   . KnownSymRep rs
  => SU2Element
  -> RepV rs
  -> RepV rs
actRep g = go (symRepSing @rs)
  where
    go :: forall rs'. SRep rs' -> RepV rs' -> RepV rs'
    go SRepNil RNil = RNil
    go (SRepCons e μ rest) (RCons v rs) =
      RCons (actSector e μ g v) (go rest rs)
    go _ _ = error "actRep: spine / singleton mismatch"

--------------------------------------------------------------------------------
-- Application (compact closed evaluation)
--
-- Given @f ∈ Mor r q = Dual r ⊗ q@ and @x ∈ r@:
--
--   1. inject:   r ⊗ (Dual r ⊗ q)     — fuse @f@ first so 'Tensor' stays leaf×leaf
--   2. assoc:    (r ⊗ Dual r) ⊗ q     — F-move / associator (blocker: no Symbolic fmove yet)
--   3. cup:      Unit ⊗ q             — evaluation @r ⊗ Dual r → Unit@ on the left
--   4. unitor:   q                    — left unitor @Unit ⊗ q → q@
--
-- | Bodies for @assocApply@ / @cup@ / @cupApply@ are intentionally @undefined@
-- (F-move and singlet counit). @injectApply@ and @lunitApply@ are implemented.
--------------------------------------------------------------------------------

-- | Step 1 target: @r ⊗ Fuse(Mor r q)@ (Mor fused to atoms so 'Tensor' applies).
type ApplyInject (r :: Rep) (q :: Rep) = Tensor r (Fuse (Mor r q))

-- | Step 2 target: @(Fuse (r ⊗ Dual r)) ⊗ q@.
type ApplyAssoc (r :: Rep) (q :: Rep) = Tensor (Fuse (Tensor r (Dual r))) q

-- | Step 3 target: @Unit ⊗ q@.
type ApplyCupped (r :: Rep) (q :: Rep) = Tensor Unit q

-- | Left-inject the object into the morphism: @x ⊗ f@.
injectApply
  :: forall r q
   . ( FuseRawSpine (Mor r q)
     , KnownSymRep (FuseRepRaw (Mor r q))
     , CoalesceSpine (FuseRepRaw (Mor r q))
     , KnownAtomRep r
     , KnownAtomRep (Fuse (Mor r q))
     )
  => RepV r
  -> RepV (Mor r q)
  -> RepV (ApplyInject r q)
injectApply x f = tensor x (fuse f)

-- | Reassociate toward cup-ready parenthesization @(r ⊗ Dual r) ⊗ q@.
-- Blocker: Symbolic F-move / associator on fused spines.
assocApply
  :: forall r q
   . RepV (ApplyInject r q)
  -> RepV (ApplyAssoc r q)
assocApply = undefined

-- | Cup (evaluation / counit): @Fuse (r ⊗ Dual r) → Unit@.
--
-- After Fuse undual + CG, keep the trivial channel and contract its copy
-- space (Hom) to a scalar. @j = 0@ agrees with 'cupUnfused'; spin-½ still
-- needs Condon–Shortley on undual for coherence (see
-- 'Experiments.SymbolicExamples.cupFusedSpinHalfCoherent').
cup
  :: forall r
   . ( ProjectToSymmetric (Fuse (Tensor r (Dual r)))
     , CupTrivial (FilterTrivial (Fuse (Tensor r (Dual r))))
     )
  => RepV (Fuse (Tensor r (Dual r)))
  -> RepV Unit
cup = cupTrivial . projectToSymmetric

-- | Contract a trivial-only spine (@FilterTrivial@) down to 'Unit'.
class CupTrivial (rs :: Rep) where
  cupTrivial :: RepV rs -> RepV Unit

instance CupTrivial '[] where
  cupTrivial RNil =
    RCons @('Atom 0) @('AtomM 1) (0 *^ (konst 1 ⊗ konst 1)) RNil

instance
  ( KnownNat m
  , KnownNat (m * 1)
  , HilbertSpace (C m)
  , InnerSpace (C m)
  , Scalar (C m) ~ Complex Double
  ) =>
  CupTrivial '[ '( 'Atom 0, 'AtomM m)]
  where
  cupTrivial (RCons v RNil) =
    let -- @C m ⊗ C 1 → C m@, then Frobenius against a flat dual of itself is
        -- wrong for Hom; @AtomM m@ on @j=0@ is a copy vector — pair with
        -- dualized self via Riesz on the flattened @C m@ (m=1 → |amp|²-style
        -- only if the vector was built that way). Prefer 'Prod' Hom layout.
        flat = fuseBond @m @1 $ v
        s = flat <.> flat
     in RCons @('Atom 0) @('AtomM 1) (s *^ (konst 1 ⊗ konst 1)) RNil

instance
  ( KnownNat m
  , KnownNat n
  , KnownNat (n * 1)
  , HilbertSpace (C m)
  , HilbertSpace (C n)
  , InnerSpace (C m)
  , Scalar (C m) ~ Complex Double
  , m ~ n
  ) =>
  CupTrivial '[ '( 'Atom 0, 'Prod ('AtomM m) ('AtomM n))]
  where
  cupTrivial (RCons t RNil) =
    let peeled =
          ((id ⊗^ fuseBond @n @1) . rassocMap) $ t
            :: C m ⊗ C n
        -- @n ~ m@: second factor as 'DualVector' via Hilbert self-duality.
        paired =
          (id ⊗^ (arr (LinearFunction (coerce :: C n -> DualVector (C n))))) $ peeled
        s = trace -+$> (fromTensor -+$=> (swapMap $ paired))
     in RCons @('Atom 0) @('AtomM 1) (s *^ (konst 1 ⊗ konst 1)) RNil

-- | Leaf pairing @v ⊗ DualVector v → ℂ@ (braid + fromTensor + trace).
cupUnfusedLeaf
  :: forall j m
   . ( KnownNat j
     , KnownNat m
     , KnownNat (IrrepDim j)
     , InnerSpace (ToVSector ('Atom j) ('AtomM m))
     , Scalar (ToVSector ('Atom j) ('AtomM m)) ~ Complex Double
     )
  => ToVSector
       ('Tensor ('Atom j) ('Dual ('Atom j)))
       ('Prod ('AtomM m) ('DualM ('AtomM m)))
  -> Complex Double
cupUnfusedLeaf t =
  let v =
        t
          :: ToVSector ('Atom j) ('AtomM m)
               ⊗ DualVector (ToVSector ('Atom j) ('AtomM m))
   in trace -+$> (fromTensor -+$=> (swapMap $ v))

-- | Atom-spine singleton ↦ dual-atom singleton (@Dual@ on keys).
dualAtomSing :: SRep rs -> SRep (Dual rs)
dualAtomSing SRepNil = SRepNil
dualAtomSing (SRepCons (SAtomI @j) (SMultAtom @m) rest) =
  SRepCons (SDualI (SAtomI @j)) (SMultDual (SMultAtom @m)) (dualAtomSing rest)
dualAtomSing _ = error "dualAtomSing: expected atom spine"

-- | Peel one @TensorOne@ row using a dual-atom guide (same length); @TensorOne@
-- reduces under the 'SRepCons' refinement so no 'PeelAppend' on an unreduced
-- @Dual r@ is required.
peelTensorOneAtomDual
  :: forall j m q ys
   . ( KnownNat j
     , KnownNat m
     , KnownNat (IrrepDim j)
     )
  => SRep q
  -> RepV (Append (TensorOne '( 'Atom j, 'AtomM m) q) ys)
  -> (RepV (TensorOne '( 'Atom j, 'AtomM m) q), RepV ys)
peelTensorOneAtomDual SRepNil rv = (RNil, rv)
peelTensorOneAtomDual
  (SRepCons (SDualI (SAtomI @k)) (SMultDual (SMultAtom @n)) qRest)
  (RCons v rv) =
    let (xs, ys) = peelTensorOneAtomDual @j @m qRest rv
     in (RCons v xs, ys)
peelTensorOneAtomDual _ _ =
  error "peelTensorOneAtomDual: expected dual-atom spine"

-- | Unfused cup on a full atom spine: sum over diagonal leaf cups in
-- @Tensor r (Dual r)@ (off-diagonal sectors contribute 0).
cupUnfusedRep
  :: forall r
   . KnownAtomRep r
  => RepV (Tensor r (Dual r))
  -> RepV Unit
cupUnfusedRep rv =
  RCons @('Atom 0) @('AtomM 1) (s *^ (konst 1 ⊗ konst 1)) RNil
  where
    dFull = dualAtomSing (symRepSing @r)
    s = goRows (symRepSing @r) rv

    goRows
      :: forall r'
       . SRep r'
      -> RepV (Tensor r' (Dual r))
      -> Complex Double
    goRows SRepNil RNil = 0
    goRows (SRepCons (SAtomI @j) (SMultAtom @m) rRest) rv' =
      goRowsCons @j @m rRest rv'
    goRows _ _ = error "cupUnfusedRep: expected atom spine"

    goRowsCons
      :: forall j m rest
       . ( KnownNat j
         , KnownNat m
         , KnownNat (IrrepDim j)
         )
      => SRep rest
      -> RepV (Tensor ('( 'Atom j, 'AtomM m) ': rest) (Dual r))
      -> Complex Double
    goRowsCons rRest rv' =
      let (row, restRv) = peelTensorOneAtomDual @j @m @(Dual r) @(Tensor rest (Dual r)) dFull rv'
       in goCols @j @m dFull row + goRows rRest restRv

    goCols
      :: forall j m q'
       . ( KnownNat j
         , KnownNat m
         , KnownNat (IrrepDim j)
         )
      => SRep q'
      -> RepV (TensorOne '( 'Atom j, 'AtomM m) q')
      -> Complex Double
    goCols SRepNil RNil = 0
    goCols
      (SRepCons (SDualI (SAtomI @k)) (SMultDual (SMultAtom @n)) qRest)
      (RCons t tRest) =
        let sCol = case (sameNat (Proxy @j) (Proxy @k), sameNat (Proxy @m) (Proxy @n)) of
              (Just Refl, Just Refl) -> cupUnfusedLeaf @j @m t
              _ -> 0
         in sCol + goCols @j @m qRest tRest
    goCols _ _ = error "cupUnfusedRep.goCols: expected dual-atom spine"

-- | Unfused leaf cup: @Atom ⊗ Dual Atom → Unit@ (special case of 'cupUnfusedRep').
cupUnfused
  :: forall j m
   . ( KnownNat j
     , KnownNat m
     , KnownNat (IrrepDim j)
     , InnerSpace (ToVSector ('Atom j) ('AtomM m))
     , Scalar (ToVSector ('Atom j) ('AtomM m)) ~ Complex Double
     )
  => RepV
       '[ '( 'Tensor ('Atom j) ('Dual ('Atom j))
           , 'Prod ('AtomM m) ('DualM ('AtomM m))
           )
        ]
  -> RepV Unit
cupUnfused = cupUnfusedRep @'[ '( 'Atom j, 'AtomM m)]

-- | Apply cup on the left factor of @ApplyAssoc@: @(cup ⊗ id)@.
cupApply
  :: forall r q
   . RepV (ApplyAssoc r q)
  -> RepV (ApplyCupped r q)
cupApply = undefined

-- | One sector: fuse @0 ⊗ j → j@, then flatten @'Prod ('AtomM 1) ('AtomM n) → 'AtomM n@.
lunitSector
  :: forall j n
   . ( KnownNat j
     , KnownNat n
     , KnownNat (IrrepDim j)
     , KnownNat (1 * n)
     )
  => ToVSector ('Tensor ('Atom 0) ('Atom j)) ('Prod ('AtomM 1) ('AtomM n))
  -> ToVSector ('Atom j) ('AtomM n)
lunitSector sec =
  flattenCopyProd @1 @n @(IrrepDim j)
    (fuseOneChannelProd @0 @j @j @1 @n sec)

-- | Left unitor on @Tensor Unit q@, driven by 'SRep' (atom spine).
-- Matching 'SAtomI'/'SMultAtom' refines @q@ so @Tensor Unit q@ reduces.
lunitSpine
  :: forall q
   . KnownAtomRep q
  => RepV (Tensor Unit q)
  -> RepV q
lunitSpine = go (symRepSing @q)
  where
    go :: forall q'. SRep q' -> RepV (Tensor Unit q') -> RepV q'
    go SRepNil RNil = RNil
    go (SRepCons (SAtomI @j) (SMultAtom @n) rest) (RCons v tRest) =
      RCons (lunitSector @j @n v) (go rest tRest)
    go _ _ = error "lunitSpine: expected atom spine"

-- | Left unitor: @Unit ⊗ q → q@.
lunitApply
  :: forall r q
   . KnownAtomRep q
  => RepV (ApplyCupped r q)
  -> RepV q
lunitApply = lunitSpine @q

-- | Categorical application @Mor r q → r → q@ via inject / assoc / cup / unitor.
apply
  :: forall r q
   . ( FuseRawSpine (Mor r q)
     , KnownSymRep (FuseRepRaw (Mor r q))
     , CoalesceSpine (FuseRepRaw (Mor r q))
     , KnownAtomRep r
     , KnownAtomRep (Fuse (Mor r q))
     , KnownAtomRep q
     )
  => RepV (Mor r q)
  -> RepV r
  -> RepV q
apply f x =
  lunitApply @r @q
    (cupApply @r @q (assocApply @r @q (injectApply @r @q x f)))

--------------------------------------------------------------------------------
-- Category (constrained-categories): morphisms as Hom-elements
--
-- @Sym a b@ wraps @RepV (Mor a b) = RepV (Dual a ⊗ b)@. Identity is coevaluation
-- @η ∈ Dual a ⊗ a@; composition cups the middle @b ⊗ Dual b@ (same blockers as
-- 'apply': F-move / fused cup). Objects are leaf atom spines ('AtomSpine').
--------------------------------------------------------------------------------

-- | Morphisms @a → b@ as elements of the internal Hom @Dual a ⊗ b@.
newtype Sym (a :: Rep) (b :: Rep) = Sym { unSym :: RepV (Mor a b) }

-- | Identity morphism: coevaluation @η : Unit → Dual a ⊗ a@ (as Hom element).
-- Blocker: cap / coeval (adjoint of 'cup').
idMor :: forall a. AtomSpine a => RepV (Mor a a)
idMor = undefined

--------------------------------------------------------------------------------
-- Composition (compact closed)
--
-- Given @f ∈ Mor a b = Dual a ⊗ b@ and @g ∈ Mor b c = Dual b ⊗ c@:
--
--   1. tensor:  Fuse(Mor a b) ⊗ Fuse(Mor b c)     — fuse so 'Tensor' stays leaf×leaf
--   2. assoc:   Dual a ⊗ (Fuse(b ⊗ Dual b) ⊗ c)   — F-move / associator
--   3. cup:     Dual a ⊗ (Unit ⊗ c)               — cup middle @b ⊗ Dual b@
--   4. unitor:  Dual a ⊗ c = Mor a c              — lunit on the right factor
--
-- Bodies intentionally @undefined@ (same F-move / fused cup as 'apply').
-- @tensorCompose@ is the inject analogue: fill as @tensor (fuse f) (fuse g)@
-- once 'FuseRawSpine' covers Mor spines.
--------------------------------------------------------------------------------

-- | Step 1 target: @Fuse(Mor a b) ⊗ Fuse(Mor b c)@.
type ComposeTensor (a :: Rep) (b :: Rep) (c :: Rep) =
  Tensor (Fuse (Mor a b)) (Fuse (Mor b c))

-- | Step 2 target: @Dual a ⊗ (Fuse (b ⊗ Dual b) ⊗ c)@.
type ComposeAssoc (a :: Rep) (b :: Rep) (c :: Rep) =
  Tensor (Dual a) (Tensor (Fuse (Tensor b (Dual b))) c)

-- | Step 3 target: @Dual a ⊗ (Unit ⊗ c)@.
type ComposeCupped (a :: Rep) (b :: Rep) (c :: Rep) =
  Tensor (Dual a) (Tensor Unit c)

-- | Tensor the two Hom-elements (after fusing each to an atom spine).
-- Blocker: 'FuseRawSpine' on Mor / Dual sectors (then @tensor (fuse f) (fuse g)@).
tensorCompose
  :: forall a b c
   . RepV (Mor a b)
  -> RepV (Mor b c)
  -> RepV (ComposeTensor a b c)
tensorCompose = undefined

-- | Reassociate toward cup-ready @Dual a ⊗ (b ⊗ Dual b) ⊗ c@.
-- Blocker: Symbolic F-move / associator (same as 'assocApply').
assocCompose
  :: forall a b c
   . RepV (ComposeTensor a b c)
  -> RepV (ComposeAssoc a b c)
assocCompose = undefined

-- | Cup the middle @Fuse (b ⊗ Dual b) → Unit@: @(id ⊗ (cup ⊗ id))@.
-- Blocker: fused cup (same as 'cupApply').
cupCompose
  :: forall a b c
   . RepV (ComposeAssoc a b c)
  -> RepV (ComposeCupped a b c)
cupCompose = undefined

-- | Left-unitor on the right factor: @Dual a ⊗ (Unit ⊗ c) → Dual a ⊗ c@.
-- Blocker: spine map of 'lunitSpine' under the @Dual a@ tensor factor.
lunitCompose
  :: forall a b c
   . RepV (ComposeCupped a b c)
  -> RepV (Mor a c)
lunitCompose = undefined

-- | Compact-closed composition @Hom(b,c) × Hom(a,b) → Hom(a,c)@.
composeMor
  :: forall a b c
   . ( AtomSpine a
     , AtomSpine b
     , AtomSpine c
     )
  => RepV (Mor b c)
  -> RepV (Mor a b)
  -> RepV (Mor a c)
composeMor g f =
  lunitCompose @a @b @c
    (cupCompose @a @b @c
      (assocCompose @a @b @c (tensorCompose @a @b @c f g)))

instance Category Sym where
  type Object Sym a = AtomSpine a

  id :: forall a. Object Sym a => Sym a a
  id = Sym (idMor @a)

  (.) :: forall a b c
      . ( Object Sym a
        , Object Sym b
        , Object Sym c
        )
     => Sym b c
     -> Sym a b
     -> Sym a c
  Sym g . Sym f = Sym (composeMor @a @b @c g f)

-- | Categorical swap of copy factors @C m ⊗ C n@ (irrep leg unchanged).
swapCopyProductSector
  :: forall m n d
   . ( KnownNat m
     , KnownNat n
     , KnownNat d
     )
  => (C m ⊗ C n) ⊗ C d
  -> (C n ⊗ C m) ⊗ C d
swapCopyProductSector sec = (swapMap ⊗^ id) $ sec

-- | Swap irrep legs on @((C m ⊗ C j₁) ⊗ C j₂)@ (copy leg fixed).
swapIrrepTensorSector
  :: forall m j1 j2
   . ( KnownNat m
     , KnownNat j1
     , KnownNat j2
     , KnownNat (IrrepDim j1)
     , KnownNat (IrrepDim j2)
     )
  => ((C m ⊗ C (IrrepDim j1)) ⊗ C (IrrepDim j2))
  -> ((C m ⊗ C (IrrepDim j2)) ⊗ C (IrrepDim j1))
swapIrrepTensorSector sec =
  (lassocMap . (id ⊗^ swapMap) . rassocMap) $ sec

-- | Swap both copy×irrep blocks @((C m₁ ⊗ C j₁) ⊗ (C m₂ ⊗ C j₂))@.
swapTensorProductSector
  :: forall m n j1 j2
   . ( KnownNat m
     , KnownNat n
     , KnownNat j1
     , KnownNat j2
     , KnownNat (IrrepDim j1)
     , KnownNat (IrrepDim j2)
     )
  => (C m ⊗ C (IrrepDim j1)) ⊗ (C n ⊗ C (IrrepDim j2))
  -> (C n ⊗ C (IrrepDim j2)) ⊗ (C m ⊗ C (IrrepDim j1))
swapTensorProductSector sec = swapMap $ sec

--------------------------------------------------------------------------------
-- Dual (term-level)
--
-- Map primal sectors into 'DualVector' payloads matching
-- @ToVSector ('Dual e) ('DualM μ)@. CS (SU(2)) / charge-flip (U(1)) identification
-- back to primal atoms belongs in Fuse/undual — not here.
--------------------------------------------------------------------------------

-- | Dual of a leaf atom sector → @DualVector (C m ⊗ C (j+1))@.
--
-- Canonical Riesz via 'InnerSpace': linear form @w ↦ v <.> w@ (linear in @w@),
-- then 'fromLinearForm'. Not @w ↦ w <.> v@ (antilinear in @w@) and not
-- 'euclideanNorm' (that is @coerce@, only valid when @DualVector v ~ v@).
dualAtomAtomM
  :: forall j m
   . ( KnownNat j
     , KnownNat m
     , KnownNat (IrrepDim j)
     , InnerSpace (ToVSector ('Atom j) ('AtomM m))
     , Scalar (ToVSector ('Atom j) ('AtomM m)) ~ Complex Double
     )
  => ToVSector ('Atom j) ('AtomM m)
  -> ToVSector ('Dual ('Atom j)) ('DualM ('AtomM m))
dualAtomAtomM v =
  fromLinearForm
    -+$> ( arr (LinearFunction ((v <.>)))
             :: ToVSector ('Atom j) ('AtomM m) +> Complex Double
         )

-- | Dual of an atom spine (@r ↦ Dual r@), driven by 'SRep'.
dual
  :: forall rs
   . KnownAtomRep rs
  => RepV rs
  -> RepV (Dual rs)
dual = go (symRepSing @rs)
  where
    go :: forall rs'. SRep rs' -> RepV rs' -> RepV (Dual rs')
    go SRepNil RNil = RNil
    go (SRepCons (SAtomI @j) (SMultAtom @m) rest) (RCons v rs) =
      RCons (dualAtomAtomM @j @m v) (go rest rs)
    go _ _ = error "dual: expected atom spine"

-- | Sector-level braid payload (@BraidIrrep@ / @BraidMult@).
braidSector
  :: SIrrep e
  -> SMult μ
  -> ToVSector e μ
  -> ToVSector (BraidIrrep e) (BraidMult μ)
braidSector SAtomI SMultAtom v = v
braidSector (SAtomI @j) (SMultProd (SMultAtom @m) (SMultAtom @n)) v =
  swapCopyProductSector @m @n @(IrrepDim j) v
braidSector (STensorI (SAtomI @j1) (SAtomI @j2)) (SMultAtom @m) v =
  swapIrrepTensorSector @m @j1 @j2 v
braidSector (STensorI (SAtomI @j1) (SAtomI @j2)) (SMultProd (SMultAtom @m) (SMultAtom @n)) v =
  swapTensorProductSector @m @n @j1 @j2 v
braidSector (SDualI SAtomI) (SMultDual SMultAtom) v = v
braidSector _ _ _ =
  error "braidSector: unsupported irrep/mult shape"

-- | Braid every sector in a 'RepV' spine (driven by 'SRep'; no 'BraidSpine' class).
braid
  :: forall rs
   . KnownSymRep rs
  => RepV rs
  -> RepV (Braid rs)
braid = go (symRepSing @rs)
  where
    go :: forall rs'. SRep rs' -> RepV rs' -> RepV (Braid rs')
    go SRepNil RNil = RNil
    go (SRepCons se sm rest) (RCons v rs) =
      RCons (braidSector se sm v) (go rest rs)

-- | Project a spine onto its trivial (@'Atom 0@) sectors.
--
-- Atom/@'AtomM@ keep-vs-drop still needs 'ProjectAtomOrd': @CmpNat j 0@ only
-- reduces when @j@ is in an instance head, not as a skolem from matching
-- 'SRep' atom match (unlike @Tensor Unit q@ refinement). Non-atom sectors are dropped.
class ProjectToSymmetric (rs :: Rep) where
  projectToSymmetric :: RepV rs -> RepV (FilterTrivial rs)

instance ProjectToSymmetric '[] where
  projectToSymmetric RNil = RNil

instance
  ( CmpNat j 0 ~ ord
  , ProjectAtomOrd ord j ('AtomM m) rest
  , ProjectToSymmetric rest
  ) =>
  ProjectToSymmetric ('( 'Atom j, 'AtomM m) ': rest)
  where
  projectToSymmetric (RConsAtomAtomM v rs) =
    projectAtomOrd @ord @j @('AtomM m) @rest
      v
      (projectToSymmetric rs)

instance
  ( CmpNat j 0 ~ ord
  , ProjectAtomOrd ord j ('Prod ('AtomM m) ('AtomM n)) rest
  , ProjectToSymmetric rest
  ) =>
  ProjectToSymmetric ('( 'Atom j, 'Prod ('AtomM m) ('AtomM n)) ': rest)
  where
  projectToSymmetric (RConsAtomProd v rs) =
    projectAtomOrd @ord @j @('Prod ('AtomM m) ('AtomM n)) @rest
      v
      (projectToSymmetric rs)

instance
  ( FilterTrivial ('( 'Tensor ('Atom j1) ('Atom j2), 'AtomM m) ': rest) ~ FilterTrivial rest
  , ProjectToSymmetric rest
  ) =>
  ProjectToSymmetric ('( 'Tensor ('Atom j1) ('Atom j2), 'AtomM m) ': rest)
  where
  projectToSymmetric (RConsTensorAtomM _ rs) = projectToSymmetric rs

instance
  ( FilterTrivial ('( 'Tensor ('Atom j1) ('Atom j2), 'Prod ('AtomM m) ('AtomM n)) ': rest) ~ FilterTrivial rest
  , ProjectToSymmetric rest
  ) =>
  ProjectToSymmetric ('( 'Tensor ('Atom j1) ('Atom j2), 'Prod ('AtomM m) ('AtomM n)) ': rest)
  where
  projectToSymmetric (RConsTensorProd _ rs) = projectToSymmetric rs

instance
  ( FilterTrivial ('( 'Dual ('Atom j), 'DualM ('AtomM m)) ': rest) ~ FilterTrivial rest
  , ProjectToSymmetric rest
  ) =>
  ProjectToSymmetric ('( 'Dual ('Atom j), 'DualM ('AtomM m)) ': rest)
  where
  projectToSymmetric (RConsDualAtomDualAtomM _ rs) = projectToSymmetric rs

instance
  ( FilterTrivial
      ( '( 'Tensor ('Atom j1) ('Dual ('Atom j2))
         , 'Prod ('AtomM m) ('DualM ('AtomM n))
         )
          ': rest
      )
      ~ FilterTrivial rest
  , ProjectToSymmetric rest
  ) =>
  ProjectToSymmetric
    ( '( 'Tensor ('Atom j1) ('Dual ('Atom j2))
       , 'Prod ('AtomM m) ('DualM ('AtomM n))
       )
        ': rest
    )
  where
  projectToSymmetric (RConsTensorAtomDualAtom _ rs) = projectToSymmetric rs

instance
  ( FilterTrivial
      ( '( 'Tensor ('Dual ('Atom j1)) ('Atom j2)
         , 'Prod ('DualM ('AtomM m)) ('AtomM n)
         )
          ': rest
      )
      ~ FilterTrivial rest
  , ProjectToSymmetric rest
  ) =>
  ProjectToSymmetric
    ( '( 'Tensor ('Dual ('Atom j1)) ('Atom j2)
       , 'Prod ('DualM ('AtomM m)) ('AtomM n)
       )
        ': rest
    )
  where
  projectToSymmetric (RConsTensorDualAtomAtom _ rs) = projectToSymmetric rs

-- | Keep (@'EQ@ / @j ~ 0@) or drop (@'GT@) one atom sector.
-- Rest is already 'FilterTrivial'-projected (caller responsibility).
class ProjectAtomOrd
  (ord :: Ordering)
  (j :: Nat)
  (μ :: MultExpr)
  (rest :: Rep)
 where
  projectAtomOrd
    :: ToVSector ('Atom j) μ
    -> RepV (FilterTrivial rest)
    -> RepV (FilterTrivial ('( 'Atom j, μ) ': rest))

instance
  ( j ~ 0
  ) =>
  ProjectAtomOrd 'EQ j μ rest
  where
  projectAtomOrd v rs = repCons @('Atom 0) @μ v rs

instance
  ( FilterTrivial ('( 'Atom j, μ) ': rest) ~ FilterTrivial rest
  ) =>
  ProjectAtomOrd 'GT j μ rest
  where
  projectAtomOrd _ rs = rs

-- | Braid a distributed tensor rep (@'Tensor'@).
braidTensor
  :: forall r s
   . KnownSymRep (Tensor r s)
  => RepV (Tensor r s)
  -> RepV (Braid (Tensor r s))
braidTensor = braid

--------------------------------------------------------------------------------
-- rmove (R-matrix on fused tensor)
--------------------------------------------------------------------------------

-- | SU(2) R-phase @(-1)^((j₁+j₂-j)/2)@ on one fused atom sector.
rPhaseSector
  :: forall j1 j2 j μ
   . ( KnownNat j1
     , KnownNat j2
     , KnownNat j
     , VectorSpace (ToVSector ('Atom j) μ)
     , Scalar (ToVSector ('Atom j) μ) ~ Complex Double
     )
  => ToVSector ('Atom j) μ
  -> ToVSector ('Atom j) μ
rPhaseSector v = (phase :+ 0) *^ v
  where
    phase = (-1) ^ ((tj1 + tj2 - tj) `div` 2)
    tj1 = fromIntegral (natVal (Proxy @j1)) :: Int
    tj2 = fromIntegral (natVal (Proxy @j2)) :: Int
    tj = fromIntegral (natVal (Proxy @j)) :: Int

-- | Copy-leg swap after R-phase (@'AtomM'@ fixed; @'Prod'@ legs flip).
type family RmoveMult (μ :: MultExpr) :: MultExpr where
  RmoveMult ('AtomM m) = 'AtomM m
  RmoveMult ('Prod ('AtomM m) ('AtomM n)) = 'Prod ('AtomM n) ('AtomM m)
  RmoveMult ('Prod μ1 μ2) = 'Prod (RmoveMult μ2) (RmoveMult μ1)

-- | Fused spine after R-move: irrep fixed; multiplicity via 'RmoveMult'.
type family RmoveTarget (j1 :: Nat) (j2 :: Nat) (rs :: Rep) :: Rep where
  RmoveTarget _ _ '[] = '[]
  RmoveTarget j1 j2 ('(e, μ) ': rest) =
    '(e, RmoveMult μ) ': RmoveTarget j1 j2 rest

-- | Sector-level R-move (phase + optional copy swap). Fused atom spines only.
rmoveSector
  :: forall j1 j2 e μ
   . ( KnownNat j1
     , KnownNat j2
     )
  => SIrrep e
  -> SMult μ
  -> ToVSector e μ
  -> ToVSector e (RmoveMult μ)
rmoveSector (SAtomI @j) (SMultAtom @m) v =
  rPhaseSector @j1 @j2 @j @('AtomM m) v
rmoveSector (SAtomI @j) (SMultProd (SMultAtom @m) (SMultAtom @n)) v =
  swapCopyProductSector @m @n @(IrrepDim j)
    (rPhaseSector @j1 @j2 @j @('Prod ('AtomM m) ('AtomM n)) v)
rmoveSector _ _ _ =
  error "rmoveSector: expected fused atom spine"

-- | R-move every sector in a fused 'RepV' spine (R-phase, then copy swap on @'Prod'@).
-- Driven by 'SRep' (no dedicated fused-atom singleton).
rmoveSpine
  :: forall j1 j2 rs
   . ( KnownNat j1
     , KnownNat j2
     , KnownSymRep rs
     )
  => RepV rs
  -> RepV (RmoveTarget j1 j2 rs)
rmoveSpine = go (symRepSing @rs)
  where
    go
      :: forall rs'
       . SRep rs'
      -> RepV rs'
      -> RepV (RmoveTarget j1 j2 rs')
    go SRepNil RNil = RNil
    go (SRepCons se sm rest) (RCons v rs) =
      RCons (rmoveSector @j1 @j2 se sm v) (go rest rs)

-- | Leaf braiding @r ⊗ s → s ⊗ r@ on a fused pair (@fuse ∘ braid ≅ rmove ∘ fuse@).
rmove
  :: forall j1 j2 r s
   . ( KnownNat j1
     , KnownNat j2
     , KnownSymRep (Fuse (Tensor r s))
     , RmoveTarget j1 j2 (Fuse (Tensor r s)) ~ Fuse (Braid (Tensor r s))
     )
  => RepV (Fuse (Tensor r s))
  -> RepV (Fuse (Braid (Tensor r s)))
rmove = rmoveSpine @j1 @j2 @(Fuse (Tensor r s))

-- | Same as 'rmove' on a distributed tensor rep (@'Tensor'@).
rmoveTensor
  :: forall j1 j2 r s
   . ( KnownNat j1
     , KnownNat j2
     , KnownSymRep (Fuse (Tensor r s))
     , RmoveTarget j1 j2 (Fuse (Tensor r s)) ~ Fuse (Braid (Tensor r s))
     )
  => RepV (Fuse (Tensor r s))
  -> RepV (Fuse (Braid (Tensor r s)))
rmoveTensor = rmove @j1 @j2 @r @s

--------------------------------------------------------------------------------
-- Compile-time smokes (type equalities)
--------------------------------------------------------------------------------

type family AssertEqIrrep (a :: IrrepExpr) (b :: IrrepExpr) :: Bool where
  AssertEqIrrep a a = 'True

type family AssertEqMult (a :: MultExpr) (b :: MultExpr) :: Bool where
  AssertEqMult a a = 'True

type family AssertEqSector (a :: Sector) (b :: Sector) :: Bool where
  AssertEqSector a a = 'True

type family AssertEqRep (a :: Rep) (b :: Rep) :: Bool where
  AssertEqRep a a = 'True

type family AssertEqType (a :: Type) (b :: Type) :: Bool where
  AssertEqType a a = 'True

type SmokeSector =
  '( 'Tensor ('Atom 1) ('Atom 2)
   , 'Prod ('AtomM 3) ('AtomM 5)
   )

type SmokeRep = '[SmokeSector]

type SmokeBraidSector =
  AssertEqSector
    (BraidSector SmokeSector)
    '( 'Tensor ('Atom 2) ('Atom 1)
     , 'Prod ('AtomM 5) ('AtomM 3)
     )

type SmokeBraid =
  AssertEqRep
    (Braid SmokeRep)
    '[ '( 'Tensor ('Atom 2) ('Atom 1)
        , 'Prod ('AtomM 5) ('AtomM 3)
        )
     ]

-- | @Braid (Tensor r s)@ on a leaf × leaf distribute.
type SmokeBraidTensor =
  AssertEqRep
    ( Braid
        ( Tensor
            '[ '( 'Atom 1, 'AtomM 2)]
            '[ '( 'Atom 2, 'AtomM 3)]
        )
    )
    '[ '( 'Tensor ('Atom 2) ('Atom 1), 'Prod ('AtomM 3) ('AtomM 2))]

-- | Dual of an atom is the @'Dual@ / @'DualM@ constructors (not silent self-duality).
type SmokeDualAtom =
  AssertEqSector
    (DualSector '( 'Atom 1, 'AtomM 3))
    '( 'Dual ('Atom 1), 'DualM ('AtomM 3))

-- | @(j₁ ⊗ j₂)* ≅ Dual j₂ ⊗ Dual j₁@ with copy @'Prod@ reversed (distributed dual).
type SmokeDualTensor =
  AssertEqSector
    (DualSector '( 'Tensor ('Atom 1) ('Atom 2), 'Prod ('AtomM 3) ('AtomM 5)))
    '( 'Tensor ('Dual ('Atom 2)) ('Dual ('Atom 1))
     , 'Prod ('DualM ('AtomM 5)) ('DualM ('AtomM 3))
     )

-- | Dual is involutive on a tensor sector (@Dual ∘ Dual = id@).
type SmokeDualInvolutive =
  AssertEqSector
    ( DualSector
        ( DualSector
            '( 'Tensor ('Atom 1) ('Atom 2), 'Prod ('AtomM 3) ('AtomM 5))
        )
    )
    '( 'Tensor ('Atom 1) ('Atom 2), 'Prod ('AtomM 3) ('AtomM 5))

-- | Dual of a leaf spine wraps each sector in @'Dual@ / @'DualM@.
type SmokeDualRep =
  AssertEqRep
    ( Dual
        '[ '( 'Atom 1, 'AtomM 2)
         , '( 'Atom 3, 'AtomM 1)
         ]
    )
    '[ '( 'Dual ('Atom 1), 'DualM ('AtomM 2))
     , '( 'Dual ('Atom 3), 'DualM ('AtomM 1))
     ]

-- | @Mor r q = Dual r ⊗ q@ on leaf atoms (unfused Dual×Atom distribute).
type SmokeMor =
  AssertEqRep
    ( Mor
        '[ '( 'Atom 1, 'AtomM 2)]
        '[ '( 'Atom 2, 'AtomM 3)]
    )
    '[ '( 'Tensor ('Dual ('Atom 1)) ('Atom 2)
        , 'Prod ('DualM ('AtomM 2)) ('AtomM 3)
        )
     ]

-- | Multi-sector left spine distributes over right (@Tensor@ Cartesian product).
type SmokeTensorSpine =
  AssertEqRep
    ( Tensor
        '[ '( 'Atom 1, 'AtomM 2), '( 'Atom 0, 'AtomM 1)]
        '[ '( 'Atom 2, 'AtomM 3)]
    )
    '[ '( 'Tensor ('Atom 1) ('Atom 2), 'Prod ('AtomM 2) ('AtomM 3))
     , '( 'Tensor ('Atom 0) ('Atom 2), 'Prod ('AtomM 1) ('AtomM 3))
     ]

-- | Same @'Atom 1@ sectors coalesce by adding multiplicities.
type SmokeCoalesceAtoms =
  AssertEqRep
    (Coalesce
      '[ '( 'Atom 1, 'AtomM 2)
       , '( 'Atom 1, 'AtomM 3)
       ])
    '[ '( 'Atom 1, 'AtomM 5)]

-- | Same @'Tensor@ with @'Prod@ multiplicities → @'AtomM@ of summed dims.
type SmokeCoalesceTensors =
  AssertEqRep
    (Coalesce
      '[ '( 'Tensor ('Atom 1) ('Atom 2), 'Prod ('AtomM 2) ('AtomM 3))
       , '( 'Tensor ('Atom 1) ('Atom 2), 'Prod ('AtomM 1) ('AtomM 4))
       ])
    '[ '( 'Tensor ('Atom 1) ('Atom 2), 'AtomM 10)]

-- | Distinct keys stay sorted (@'Atom' < 'Tensor'@).
type SmokeCoalesceSort =
  AssertEqRep
    (Coalesce
      '[ '( 'Tensor ('Atom 0) ('Atom 1), 'AtomM 1)
       , '( 'Atom 2, 'AtomM 1)
       ])
    '[ '( 'Atom 2, 'AtomM 1)
     , '( 'Tensor ('Atom 0) ('Atom 1), 'AtomM 1)
     ]

-- | Leaf sector @('Atom 1, 'AtomM 3)@ → @C 3 ⊗ C 2@.
type SmokeSectorAtom =
  AssertEqType
    (ToVSector ('Atom 1) ('AtomM 3))
    (C 3 ⊗ C 2)

type SmokeSectorTensor =
  AssertEqType
    (ToVSector ('Tensor ('Atom 1) ('Atom 2)) ('Prod ('AtomM 2) ('AtomM 3)))
    ((C 2 ⊗ C 2) ⊗ (C 3 ⊗ C 3))

-- | @1 ⊗ 2@ (SU2) → @j = 1, 3@ channels.
type SmokeFuseIrrep =
  AssertEqRep
    (FuseIrrep ('Tensor ('Atom 1) ('Atom 2)))
    '[ '( 'Atom 1, 'AtomM 1)
     , '( 'Atom 3, 'AtomM 1)
     ]

-- | Sector fuse tags copy multiplicity onto each CG channel.
type SmokeFuseSector =
  AssertEqRep
    (FuseSector '( 'Tensor ('Atom 1) ('Atom 2), 'Prod ('AtomM 2) ('AtomM 3)))
    '[ '( 'Atom 1, 'Prod ('AtomM 2) ('AtomM 3))
     , '( 'Atom 3, 'Prod ('AtomM 2) ('AtomM 3))
     ]

-- | Atom sector is unchanged (modulo unit mult tag).
type SmokeFuseRepAtom =
  AssertEqRep
    (Fuse '[ '( 'Atom 2, 'AtomM 5)])
    '[ '( 'Atom 2, 'AtomM 5)]

-- | @Tensor@ then @Fuse@ on two single-sector reps.
type SmokeFuseTensor =
  AssertEqRep
    ( Fuse
        ( Tensor
            '[ '( 'Atom 1, 'AtomM 2)]
            '[ '( 'Atom 2, 'AtomM 3)]
        )
    )
    '[ '( 'Atom 1, 'Prod ('AtomM 2) ('AtomM 3))
     , '( 'Atom 3, 'Prod ('AtomM 2) ('AtomM 3))
     ]

-- | @Fuse (Braid (Tensor …))@ swaps tensor legs and copy product.
type SmokeFuseBraidTensor =
  AssertEqRep
    ( Fuse
        ( Braid
            ( Tensor
                '[ '( 'Atom 1, 'AtomM 2)]
                '[ '( 'Atom 2, 'AtomM 3)]
            )
        )
    )
    '[ '( 'Atom 1, 'Prod ('AtomM 3) ('AtomM 2))
     , '( 'Atom 3, 'Prod ('AtomM 3) ('AtomM 2))
     ]

-- | 'RmoveTarget' on a leaf fused tensor matches @Fuse (Braid (Tensor …))@.
type SmokeRmoveTarget =
  AssertEqRep
    ( RmoveTarget
        1
        2
        ( Fuse
            ( Tensor
                '[ '( 'Atom 1, 'AtomM 2)]
                '[ '( 'Atom 2, 'AtomM 3)]
            )
        )
    )
    ( Fuse
        ( Braid
            ( Tensor
                '[ '( 'Atom 1, 'AtomM 2)]
                '[ '( 'Atom 2, 'AtomM 3)]
            )
        )
    )

-- | Swapped tensor legs yield the same fused atom spine (@SU(2)@ CG symmetry).
type SmokeFusedLeafSym =
  AssertEqRep
    ( Coalesce
        (TagMult ('AtomM 6) (FuseIrrep ('Tensor ('Atom 2) ('Atom 1))))
    )
    ( Coalesce
        (TagMult ('AtomM 6) (FuseIrrep ('Tensor ('Atom 1) ('Atom 2))))
    )

-- | Reference flat fuse layout for @1 ⊗ 2@, @m = 2@, @n = 3@.
type SmokeFusedLeaf12 =
  AssertEqRep
    (Coalesce (TagMult ('AtomM 6) (FuseIrrep ('Tensor ('Atom 1) ('Atom 2)))))
    '[ '( 'Atom 1, 'AtomM 6)
     , '( 'Atom 3, 'AtomM 6)
     ]

-- | 'FilterTrivial' keeps only @'Atom 0@ sectors.
type SmokeFilterTrivial =
  AssertEqRep
    ( FilterTrivial
        '[ '( 'Atom 1, 'AtomM 2)
         , '( 'Atom 0, 'AtomM 3)
         , '( 'Tensor ('Atom 1) ('Atom 1), 'Prod ('AtomM 1) ('AtomM 1))
         , '( 'Atom 0, 'Prod ('AtomM 2) ('AtomM 2))
         ]
    )
    '[ '( 'Atom 0, 'AtomM 3)
     , '( 'Atom 0, 'Prod ('AtomM 2) ('AtomM 2))
     ]

-- | 'RepV' spine type is stable under its own index.
type SmokeRepVSpine =
  AssertEqType
    (RepV '[ '( 'Atom 1, 'AtomM 2), '( 'Tensor ('Atom 0) ('Atom 1), 'AtomM 1)])
    (RepV '[ '( 'Atom 1, 'AtomM 2), '( 'Tensor ('Atom 0) ('Atom 1), 'AtomM 1)])

smokeBraidSector :: Proxy SmokeBraidSector
smokeBraidSector = Proxy

smokeBraid :: Proxy SmokeBraid
smokeBraid = Proxy

smokeBraidTensor :: Proxy SmokeBraidTensor
smokeBraidTensor = Proxy

smokeDualAtom :: Proxy SmokeDualAtom
smokeDualAtom = Proxy

smokeDualTensor :: Proxy SmokeDualTensor
smokeDualTensor = Proxy

smokeDualInvolutive :: Proxy SmokeDualInvolutive
smokeDualInvolutive = Proxy

smokeDualRep :: Proxy SmokeDualRep
smokeDualRep = Proxy

smokeMor :: Proxy SmokeMor
smokeMor = Proxy

smokeTensorSpine :: Proxy SmokeTensorSpine
smokeTensorSpine = Proxy

smokeCoalesceAtoms :: Proxy SmokeCoalesceAtoms
smokeCoalesceAtoms = Proxy

smokeCoalesceTensors :: Proxy SmokeCoalesceTensors
smokeCoalesceTensors = Proxy

smokeCoalesceSort :: Proxy SmokeCoalesceSort
smokeCoalesceSort = Proxy

smokeSectorAtom :: Proxy SmokeSectorAtom
smokeSectorAtom = Proxy

smokeSectorTensor :: Proxy SmokeSectorTensor
smokeSectorTensor = Proxy

smokeFuseIrrep :: Proxy SmokeFuseIrrep
smokeFuseIrrep = Proxy

smokeFuseSector :: Proxy SmokeFuseSector
smokeFuseSector = Proxy

smokeFuseRepAtom :: Proxy SmokeFuseRepAtom
smokeFuseRepAtom = Proxy

smokeFuseTensor :: Proxy SmokeFuseTensor
smokeFuseTensor = Proxy

smokeFuseBraidTensor :: Proxy SmokeFuseBraidTensor
smokeFuseBraidTensor = Proxy

smokeRmoveTarget :: Proxy SmokeRmoveTarget
smokeRmoveTarget = Proxy

smokeFusedLeafSym :: Proxy SmokeFusedLeafSym
smokeFusedLeafSym = Proxy

smokeFusedLeaf12 :: Proxy SmokeFusedLeaf12
smokeFusedLeaf12 = Proxy

smokeFilterTrivial :: Proxy SmokeFilterTrivial
smokeFilterTrivial = Proxy

smokeRepVSpine :: Proxy SmokeRepVSpine
smokeRepVSpine = Proxy
