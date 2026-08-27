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
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))
import Data.VectorSpace (Scalar, VectorSpace ((*^)))
import GHC.TypeLits (CmpNat, KnownNat, Nat, natVal, type (*), type (+))
import Control.Arrow.Constrained (($))
import Control.Category.Constrained.Prelude (Category (..))
import Experiments.SU2 (TensorIrrepRepSU2)
import Math.LinearMap.Category
  ( DualVector
  , pattern LinearFunction
  , type (+>)
  , type (⊗)
  , (⊗)
  )
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static (C)
import Symmetry.Utils (Append)
import Control.Arrow.Constrained (arr)
import Symmetry.CG.SU2 (fuseCGChannel)
import TensorNetwork.Categorical
  ( flattenCopyProd
  , flattenTensorProdCopy
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
-- Unfused duals are real @'Dual@ constructors; 'ToVSector' maps them to
-- 'DualVector'. The SU(2) CS / U(1) charge-flip identification into ordinary
-- @'Atom@ spines is a later Fuse (or undual) step — not a silent type equality.
--------------------------------------------------------------------------------

-- | Dual of an irrep expression (involutive; reverses tensor factors).
type family DualIrrep (e :: IrrepExpr) :: IrrepExpr where
  DualIrrep ('Dual e) = e
  DualIrrep ('Atom j) = 'Dual ('Atom j)
  DualIrrep ('Tensor e1 e2) = 'Dual ('Tensor e2 e1)

-- | Dual of a multiplicity expression (involutive; reverses products).
type family DualMult (μ :: MultExpr) :: MultExpr where
  DualMult ('DualM μ) = μ
  DualMult ('AtomM m) = 'DualM ('AtomM m)
  DualMult ('Prod μ1 μ2) = 'DualM ('Prod μ2 μ1)

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

-- | Tag every CG channel with unit multiplicity (irrep-only fuse).
type family AtomsFromCG (cg :: [(Nat, Nat)]) :: Rep where
  AtomsFromCG '[] = '[]
  AtomsFromCG ('(j, _) ': rest) = '( 'Atom j, 'AtomM 1) ': AtomsFromCG rest

-- | Fuse one 'IrrepExpr' to a 'Rep' of atoms (@'AtomM 1@ on each channel).
-- Dual identification (CS / charge flip) is intentionally not here yet.
type family FuseIrrep (e :: IrrepExpr) :: Rep where
  FuseIrrep ('Atom j) = '[ '( 'Atom j, 'AtomM 1)]
  FuseIrrep ('Tensor ('Atom j1) ('Atom j2)) =
    AtomsFromCG (TensorIrrepRepSU2 j1 j2)

-- | Attach a sector multiplicity to every atom in a fused irrep spine.
type family TagMult (μ :: MultExpr) (rs :: Rep) :: Rep where
  TagMult μ '[] = '[]
  TagMult μ ('( 'Atom j, _) ': rest) = '( 'Atom j, μ) ': TagMult μ rest

-- | Fuse one sector: CG the irrep part, keep (or tensor) the copy part.
type family FuseSector (s :: Sector) :: Rep where
  FuseSector '(e, μ) = TagMult μ (FuseIrrep e)

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

-- | Constraint: spine is leaf atoms with @'AtomM@ multiplicities (tensor domain).
type family AtomSpine (rs :: Rep) :: Constraint where
  AtomSpine '[] = ()
  AtomSpine ('( 'Atom j, 'AtomM m) ': rest) =
    ( KnownNat j
    , KnownNat m
    , KnownNat (IrrepDim j)
    , AtomSpine rest
    )

--------------------------------------------------------------------------------
-- Atom-spine / dual-atom-spine singletons
--
-- Bespoke, like 'Symmetry.RepSingleton.SRep': enough to case on leaf spines and
-- refine type-family indices (@Tensor Unit q@, @Tensor (Dual r) q@, etc.) without
-- a walk class per operation. Not full @singletons@ for @IrrepExpr@.
--
-- Motivation: @RepV@ constructor explosion if @IrrepExpr@ recursion is mirrored
-- in the GADT; a spine singleton + uniform sector payload is the long-term exit.
--------------------------------------------------------------------------------

-- | Runtime witness for an atom-only spine (@'Atom@ / @'AtomM@).
data SAtomRep (rs :: Rep) where
  SAtomNil :: SAtomRep '[]
  SAtomCons
    :: forall j m rest
     . ( KnownNat j
       , KnownNat m
       , KnownNat (IrrepDim j)
       )
    => SAtomRep rest
    -> SAtomRep ('( 'Atom j, 'AtomM m) ': rest)

-- | Materialize 'SAtomRep' for a statically known atom spine.
class KnownAtomRep (rs :: Rep) where
  atomRepSing :: SAtomRep rs

instance KnownAtomRep '[] where
  atomRepSing = SAtomNil

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim j)
  , KnownAtomRep rest
  ) =>
  KnownAtomRep ('( 'Atom j, 'AtomM m) ': rest)
  where
  atomRepSing = SAtomCons @j @m (atomRepSing @rest)

-- | Runtime witness for a dual-atom spine (@'Dual ('Atom j)@ / @'DualM ('AtomM m)@).
data SDualAtomRep (rs :: Rep) where
  SDualAtomNil :: SDualAtomRep '[]
  SDualAtomCons
    :: forall j m rest
     . ( KnownNat j
       , KnownNat m
       , KnownNat (IrrepDim j)
       )
    => SDualAtomRep rest
    -> SDualAtomRep ('( 'Dual ('Atom j), 'DualM ('AtomM m)) ': rest)

-- | Materialize 'SDualAtomRep' for a statically known dual-atom spine.
class KnownDualAtomRep (rs :: Rep) where
  dualAtomRepSing :: SDualAtomRep rs

instance KnownDualAtomRep '[] where
  dualAtomRepSing = SDualAtomNil

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim j)
  , KnownDualAtomRep rest
  ) =>
  KnownDualAtomRep ('( 'Dual ('Atom j), 'DualM ('AtomM m)) ': rest)
  where
  dualAtomRepSing = SDualAtomCons @j @m (dualAtomRepSing @rest)

--------------------------------------------------------------------------------
-- Term-level spine ('RepV') and fusion
--
-- Uniform @RCons@: sector shape lives in the type index @'(e, μ)@, not in a
-- GADT constructor per leaf shape. Old constructor names are pattern synonyms
-- for call sites; discriminating walks match @RCons @e @μ@.
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
  :: ()
  => (e ~ 'Atom j, μ ~ 'AtomM m)
  => ToVSector ('Atom j) ('AtomM m)
  -> RepV rest
  -> RepV ('( 'Atom j, 'AtomM m) ': rest)
pattern RConsAtomAtomM v rs = RCons @('Atom j) @('AtomM m) v rs

pattern RConsAtomProd
  :: ()
  => (e ~ 'Atom j, μ ~ 'Prod ('AtomM m) ('AtomM n))
  => ToVSector ('Atom j) ('Prod ('AtomM m) ('AtomM n))
  -> RepV rest
  -> RepV ('( 'Atom j, 'Prod ('AtomM m) ('AtomM n)) ': rest)
pattern RConsAtomProd v rs =
  RCons @('Atom j) @('Prod ('AtomM m) ('AtomM n)) v rs

pattern RConsTensorAtomM
  :: ()
  => (e ~ 'Tensor ('Atom j1) ('Atom j2), μ ~ 'AtomM m)
  => ToVSector ('Tensor ('Atom j1) ('Atom j2)) ('AtomM m)
  -> RepV rest
  -> RepV ('( 'Tensor ('Atom j1) ('Atom j2), 'AtomM m) ': rest)
pattern RConsTensorAtomM v rs =
  RCons @('Tensor ('Atom j1) ('Atom j2)) @('AtomM m) v rs

pattern RConsTensorProd
  :: ()
  => (e ~ 'Tensor ('Atom j1) ('Atom j2), μ ~ 'Prod ('AtomM m) ('AtomM n))
  => ToVSector ('Tensor ('Atom j1) ('Atom j2)) ('Prod ('AtomM m) ('AtomM n))
  -> RepV rest
  -> RepV ('( 'Tensor ('Atom j1) ('Atom j2), 'Prod ('AtomM m) ('AtomM n)) ': rest)
pattern RConsTensorProd v rs =
  RCons @('Tensor ('Atom j1) ('Atom j2)) @('Prod ('AtomM m) ('AtomM n)) v rs

pattern RConsDualAtomDualAtomM
  :: ()
  => (e ~ 'Dual ('Atom j), μ ~ 'DualM ('AtomM m))
  => ToVSector ('Dual ('Atom j)) ('DualM ('AtomM m))
  -> RepV rest
  -> RepV ('( 'Dual ('Atom j), 'DualM ('AtomM m)) ': rest)
pattern RConsDualAtomDualAtomM v rs =
  RCons @('Dual ('Atom j)) @('DualM ('AtomM m)) v rs

pattern RConsTensorAtomDualAtom
  :: ()
  => ( e ~ 'Tensor ('Atom j1) ('Dual ('Atom j2))
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
  :: ()
  => ( e ~ 'Tensor ('Dual ('Atom j1)) ('Atom j2)
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

{-# COMPLETE RNil, RCons :: RepV #-}

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

-- | Fuse one sector to its @FuseSector@ spine (dispatches on @e@/@μ@).
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

-- | Insert one sector into a coalesced spine (sort + merge on equal keys).
class InsertSpine (e :: IrrepExpr) (μ :: MultExpr) (rs :: Rep) where
  insertSpine
    :: ToVSector e μ
    -> RepV rs
    -> RepV (InsertSector e μ rs)

instance InsertSpine e μ '[] where
  insertSpine sv RNil = repCons @e @μ sv RNil

instance
  ( CmpIrrep e e2 ~ ord
  , InsertCompared ord e μ e2 μ2 rest
  ) =>
  InsertSpine e μ ('(e2, μ2) ': rest)
  where
  insertSpine sv (RCons sv2 restR) =
    insertCompared @ord @e @μ @e2 @μ2 sv sv2 restR

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

-- | Constraints for 'fuseRaw' on a spine.
type family FuseRawSpine (rs :: Rep) :: Constraint where
  FuseRawSpine '[] = ()
  FuseRawSpine ('(e, μ) ': rest) =
    ( FuseOneSector e μ
    , FuseRawSpine rest
    )

-- | Constraints for 'coalesce' on a spine.
type family CoalesceSpine (rs :: Rep) :: Constraint where
  CoalesceSpine '[] = ()
  CoalesceSpine ('(e, μ) ': rest) =
    ( InsertSpine e μ (Coalesce rest)
    , CoalesceSpine rest
    )

-- | CG-fuse every sector in a spine, append (no coalesce).
fuseRaw
  :: FuseRawSpine rs
  => RepV rs
  -> RepV (FuseRepRaw rs)
fuseRaw RNil = RNil
fuseRaw (RCons @e @μ sv rs) =
  appendRepV (fuseOneSector @e @μ sv) (fuseRaw rs)

-- | Sort + merge equal @'IrrepExpr'@ keys on a spine.
coalesce
  :: CoalesceSpine rs
  => RepV rs
  -> RepV (Coalesce rs)
coalesce RNil = RNil
coalesce (RCons @e @μ sv rs) =
  insertSpine @e @μ sv (coalesce rs)


fuse :: ( FuseRawSpine rs
     , CoalesceSpine (FuseRepRaw rs)
     )
  => RepV rs
  -> RepV (Fuse rs)
fuse rv =
  coalesce (fuseRaw rv)

-- | CG fuse a distributed tensor rep (@'Tensor'@).
fuseTensor
  :: ( FuseRawSpine (Tensor r s)
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

-- | Pair one left atom sector with a right atom spine ('SAtomRep').
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
tensorOneAtom s1 = go (atomRepSing @q)
  where
    go :: forall q'. SAtomRep q' -> RepV q' -> RepV (TensorOne '( 'Atom j, 'AtomM m) q')
    go SAtomNil RNil = RNil
    go (SAtomCons @j2 @n rest) (RCons s2 qRest) =
      RCons (s1 ⊗ s2) (go rest qRest)

-- | Atom×atom Cartesian tensor via 'SAtomRep' (replaces 'TensorOneSpine' on atoms).
tensorAtom
  :: forall r q
   . ( KnownAtomRep r
     , KnownAtomRep q
     )
  => RepV r
  -> RepV q
  -> RepV (Tensor r q)
tensorAtom r q = go (atomRepSing @r) r
  where
    go :: forall r'. SAtomRep r' -> RepV r' -> RepV (Tensor r' q)
    go SAtomNil RNil = RNil
    go (SAtomCons @j @m rest) (RCons s1 rRest) =
      appendRepV (tensorOneAtom @j @m s1 q) (go rest rRest)

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
tensorOneDualAtom s1 = go (atomRepSing @q)
  where
    go
      :: forall q'
       . SAtomRep q'
      -> RepV q'
      -> RepV (TensorOne '( 'Dual ('Atom j), 'DualM ('AtomM m)) q')
    go SAtomNil RNil = RNil
    go (SAtomCons @_ @_ rest) (RCons s2 qRest) =
      RCons (s1 ⊗ s2) (go rest qRest)

-- | Dual-atom × atom Cartesian tensor via 'SDualAtomRep' / 'SAtomRep'.
tensorDualAtom
  :: forall r q
   . ( KnownDualAtomRep r
     , KnownAtomRep q
     )
  => RepV r
  -> RepV q
  -> RepV (Tensor r q)
tensorDualAtom r q = go (dualAtomRepSing @r) r
  where
    go :: forall r'. SDualAtomRep r' -> RepV r' -> RepV (Tensor r' q)
    go SDualAtomNil RNil = RNil
    go (SDualAtomCons @j @m rest) (RCons s1 rRest) =
      appendRepV (tensorOneDualAtom @j @m s1 q) (go rest rRest)

-- | Leaf×leaf tensor of two spines ('Tensor' type family).
-- Atom×atom and dual×atom are singleton-driven; no walk class per side.
class TensorSpine (r :: Rep) (q :: Rep) where
  tensor :: RepV r -> RepV q -> RepV (Tensor r q)

instance (KnownAtomRep r, KnownAtomRep q) => TensorSpine r q where
  tensor = tensorAtom

instance
  ( KnownDualAtomRep ('( 'Dual ('Atom j), 'DualM ('AtomM m)) ': rest)
  , KnownAtomRep q
  ) =>
  TensorSpine ('( 'Dual ('Atom j), 'DualM ('AtomM m)) ': rest) q
  where
  tensor = tensorDualAtom

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
     , CoalesceSpine (FuseRepRaw (Mor r q))
     , TensorSpine r (Fuse (Mor r q))
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
-- Blocker: fused cup + Dual identification in Fuse.
cup
  :: forall r
   . RepV (Fuse (Tensor r (Dual r)))
  -> RepV Unit
cup = undefined

-- | Unfused leaf cup: @Atom ⊗ Dual Atom → Unit@ via linearmap duals.
--
-- Blocker: for @v = C m ⊗ C (j+1)@, @DualVector v = C m +> DualVector (C (j+1))@
-- and @applyDualVector@ / @(<.>^)@ disagree with @InnerSpace (<.>)@ on Complex
-- (e.g. @x=3+4i@ gives @x<.>x = 25@ but @(euclideanNorm<$|x)<.>^x = -7+24i@).
-- Need a typed flatten-to-@C (m·(j+1))@ Riesz cup, or a linearmap DualVector
-- fix for complex tensor products — co-plan before implementing.
cupUnfused
  :: forall j m
   . ( KnownNat j
     , KnownNat m
     , KnownNat (IrrepDim j)
     )
  => RepV
       '[ '( 'Tensor ('Atom j) ('Dual ('Atom j))
           , 'Prod ('AtomM m) ('DualM ('AtomM m))
           )
        ]
  -> RepV Unit
cupUnfused = undefined

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

-- | Left unitor on @Tensor Unit q@, driven by 'SAtomRep' (no 'LunitSpine' class).
-- Matching the singleton refines @q@ so @Tensor Unit q@ reduces; then the
-- @RCons@ payload type-checks against @lunitSector@.
lunitSpine
  :: forall q
   . KnownAtomRep q
  => RepV (Tensor Unit q)
  -> RepV q
lunitSpine = go (atomRepSing @q)
  where
    go :: forall q'. SAtomRep q' -> RepV (Tensor Unit q') -> RepV q'
    go SAtomNil RNil = RNil
    go (SAtomCons @j @n rest) (RCons v tRest) =
      RCons (lunitSector @j @n v) (go rest tRest)

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
     , CoalesceSpine (FuseRepRaw (Mor r q))
     , TensorSpine r (Fuse (Mor r q))
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

-- | Riesz dual of a leaf atom sector → @DualVector (C m ⊗ C (j+1))@.
--
-- Blocker: same DualVector/@(<.>^)@ mismatch as 'cupUnfused' for Complex
-- tensor products. Stub until flatten-Riesz or linearmap fix is agreed.
dualAtomAtomM
  :: forall j m
   . ( KnownNat j
     , KnownNat m
     , KnownNat (IrrepDim j)
     )
  => ToVSector ('Atom j) ('AtomM m)
  -> ToVSector ('Dual ('Atom j)) ('DualM ('AtomM m))
dualAtomAtomM = undefined

-- | Dual of an atom spine (@r ↦ Dual r@), driven by 'SAtomRep'.
dual
  :: forall rs
   . KnownAtomRep rs
  => RepV rs
  -> RepV (Dual rs)
dual = go (atomRepSing @rs)
  where
    go :: forall rs'. SAtomRep rs' -> RepV rs' -> RepV (Dual rs')
    go SAtomNil RNil = RNil
    go (SAtomCons @j @m rest) (RCons v rs) =
      RCons (dualAtomAtomM @j @m v) (go rest rs)

-- | Sector-level braid on payloads (@BraidIrrep@ / @BraidMult@).
class BraidSectorV (e :: IrrepExpr) (μ :: MultExpr) where
  braidSectorV
    :: ToVSector e μ
    -> ToVSector (BraidIrrep e) (BraidMult μ)

instance BraidSectorV ('Atom j) ('AtomM m) where
  braidSectorV = id

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim j)
  ) =>
  BraidSectorV ('Atom j) ('Prod ('AtomM m) ('AtomM n))
  where
  braidSectorV = swapCopyProductSector @m @n @(IrrepDim j)

instance
  ( KnownNat m
  , KnownNat j1
  , KnownNat j2
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  ) =>
  BraidSectorV ('Tensor ('Atom j1) ('Atom j2)) ('AtomM m)
  where
  braidSectorV = swapIrrepTensorSector @m @j1 @j2

instance
  ( KnownNat m
  , KnownNat n
  , KnownNat j1
  , KnownNat j2
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  ) =>
  BraidSectorV ('Tensor ('Atom j1) ('Atom j2)) ('Prod ('AtomM m) ('AtomM n))
  where
  braidSectorV = swapTensorProductSector @m @n @j1 @j2

instance BraidSectorV ('Dual ('Atom j)) ('DualM ('AtomM m)) where
  braidSectorV = id

-- | Constraints for braiding every sector in a spine.
type family BraidSpine (rs :: Rep) :: Constraint where
  BraidSpine '[] = ()
  BraidSpine ('(e, μ) ': rest) =
    ( BraidSectorV e μ
    , BraidSpine rest
    )

-- | Project a spine onto its trivial (@'Atom 0@) sectors.
--
-- Atom/@'AtomM@ keep-vs-drop still needs 'ProjectAtomOrd': @CmpNat j 0@ only
-- reduces when @j@ is in an instance head, not as a skolem from matching
-- 'SAtomRep' (unlike @Tensor Unit q@ refinement). Non-atom sectors are dropped.
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
  projectToSymmetric (RCons v rs) =
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
  projectToSymmetric (RCons v rs) =
    projectAtomOrd @ord @j @('Prod ('AtomM m) ('AtomM n)) @rest
      v
      (projectToSymmetric rs)

instance
  ( FilterTrivial ('( 'Tensor ('Atom j1) ('Atom j2), 'AtomM m) ': rest) ~ FilterTrivial rest
  , ProjectToSymmetric rest
  ) =>
  ProjectToSymmetric ('( 'Tensor ('Atom j1) ('Atom j2), 'AtomM m) ': rest)
  where
  projectToSymmetric (RCons _ rs) = projectToSymmetric rs

instance
  ( FilterTrivial ('( 'Tensor ('Atom j1) ('Atom j2), 'Prod ('AtomM m) ('AtomM n)) ': rest) ~ FilterTrivial rest
  , ProjectToSymmetric rest
  ) =>
  ProjectToSymmetric ('( 'Tensor ('Atom j1) ('Atom j2), 'Prod ('AtomM m) ('AtomM n)) ': rest)
  where
  projectToSymmetric (RCons _ rs) = projectToSymmetric rs

instance
  ( FilterTrivial ('( 'Dual ('Atom j), 'DualM ('AtomM m)) ': rest) ~ FilterTrivial rest
  , ProjectToSymmetric rest
  ) =>
  ProjectToSymmetric ('( 'Dual ('Atom j), 'DualM ('AtomM m)) ': rest)
  where
  projectToSymmetric (RCons _ rs) = projectToSymmetric rs

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
  projectToSymmetric (RCons _ rs) = projectToSymmetric rs

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
  projectToSymmetric (RCons _ rs) = projectToSymmetric rs

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

-- | Braid every sector in a 'RepV' spine.
braid
  :: forall rs
   . BraidSpine rs
  => RepV rs
  -> RepV (Braid rs)
braid RNil = RNil
braid (RCons @e @μ v rs) =
  RCons (braidSectorV @e @μ v) (braid rs)

-- | Braid a distributed tensor rep (@'Tensor'@).
braidTensor
  :: forall r s
   . BraidSpine (Tensor r s)
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

-- | Sector-level R-move (phase + optional copy swap).
class RmoveSectorV (j1 :: Nat) (j2 :: Nat) (e :: IrrepExpr) (μ :: MultExpr) where
  rmoveSectorV
    :: ToVSector e μ
    -> ToVSector e (RmoveMult μ)

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat j
  , VectorSpace (ToVSector ('Atom j) ('AtomM m))
  , Scalar (ToVSector ('Atom j) ('AtomM m)) ~ Complex Double
  ) =>
  RmoveSectorV j1 j2 ('Atom j) ('AtomM m)
  where
  rmoveSectorV = rPhaseSector @j1 @j2 @j @('AtomM m)

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat j
  , KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim j)
  , VectorSpace (ToVSector ('Atom j) ('Prod ('AtomM m) ('AtomM n)))
  , Scalar (ToVSector ('Atom j) ('Prod ('AtomM m) ('AtomM n))) ~ Complex Double
  , ToVSector ('Atom j) ('Prod ('AtomM m) ('AtomM n))
      ~ (C m ⊗ C n) ⊗ C (IrrepDim j)
  ) =>
  RmoveSectorV j1 j2 ('Atom j) ('Prod ('AtomM m) ('AtomM n))
  where
  rmoveSectorV v =
    swapCopyProductSector @m @n @(IrrepDim j)
      (rPhaseSector @j1 @j2 @j @('Prod ('AtomM m) ('AtomM n)) v)

-- | Constraints for R-moving every sector in a fused spine.
type family RmoveSpine (j1 :: Nat) (j2 :: Nat) (rs :: Rep) :: Constraint where
  RmoveSpine _ _ '[] = ()
  RmoveSpine j1 j2 ('(e, μ) ': rest) =
    ( RmoveSectorV j1 j2 e μ
    , RmoveSpine j1 j2 rest
    )

-- | R-move every sector in a fused 'RepV' spine (R-phase, then copy swap on @'Prod'@).
rmoveSpine
  :: forall j1 j2 rs
   . RmoveSpine j1 j2 rs
  => RepV rs
  -> RepV (RmoveTarget j1 j2 rs)
rmoveSpine RNil = RNil
rmoveSpine (RCons @e @μ v rs) =
  RCons (rmoveSectorV @j1 @j2 @e @μ v) (rmoveSpine @j1 @j2 rs)

-- | Leaf braiding @r ⊗ s → s ⊗ r@ on a fused pair (@fuse ∘ braid ≅ rmove ∘ fuse@).
rmove
  :: forall j1 j2 r s
   . ( RmoveSpine j1 j2 (Fuse (Tensor r s))
     , RmoveTarget j1 j2 (Fuse (Tensor r s)) ~ Fuse (Braid (Tensor r s))
     )
  => RepV (Fuse (Tensor r s))
  -> RepV (Fuse (Braid (Tensor r s)))
rmove = rmoveSpine @j1 @j2 @(Fuse (Tensor r s))

-- | Same as 'rmove' on a distributed tensor rep (@'Tensor'@).
rmoveTensor
  :: forall j1 j2 r s
   . ( RmoveSpine j1 j2 (Fuse (Tensor r s))
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

-- | @(j₁ ⊗ j₂)* ≅ Dual (j₂ ⊗ j₁)@ with copy product reversed under @'DualM@.
type SmokeDualTensor =
  AssertEqSector
    (DualSector '( 'Tensor ('Atom 1) ('Atom 2), 'Prod ('AtomM 3) ('AtomM 5)))
    '( 'Dual ('Tensor ('Atom 2) ('Atom 1)), 'DualM ('Prod ('AtomM 5) ('AtomM 3)))

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
