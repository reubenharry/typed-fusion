{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Green-field symbolic SU(2) reps: flat irrep @'Tensor j1 j2@ and flat
-- multiplicity @'Prod m n@.
--
-- Fusion-tree association is temporal (@Fuse@ then tensor again), so tensors
-- are always leaf×leaf. 'Coalesce' merges same-'IrrepExpr' sectors by adding
-- evaluated multiplicities into an @'AtomM@. 'RepV' is the indexed term-level
-- spine; 'KnownSymbolicRep' drives fuse and coalesce on it directly.
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
import Data.VectorSpace (Scalar, VectorSpace, (*^))
import GHC.TypeLits (CmpNat, KnownNat, Nat, natVal, type (*), type (+))
import Control.Arrow.Constrained (($))
import Control.Category.Constrained.Prelude (Category (..))
import Experiments.SU2 (TensorIrrepRepSU2)
import Math.LinearMap.Category (type (⊗), (⊗), LSpace, TensorSpace)
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.LinearMap.Category.Instances ()
import Numeric.LinearAlgebra.Static (C)
import Symmetry.Utils (Append)
import Control.Arrow.Constrained (arr)
import Math.LinearMap.Category (pattern LinearFunction)
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

-- | SU(2) irrep expression: a leaf @j@, or a flat binary tensor @j1 :⊗: j2@.
data IrrepExpr
  = Atom Nat
  | Tensor Nat Nat

-- | Formal multiplicity: a leaf @m@, or a flat product @m × n@.
data MultExpr
  = AtomM Nat
  | Prod Nat Nat

type Sector = (IrrepExpr, MultExpr)
type Rep = [Sector]

--------------------------------------------------------------------------------
-- Braid (swap tensor factors on each sector)
--------------------------------------------------------------------------------

-- | Swap irrep / copy factors sector-wise (@'Tensor j1 j2'@ ↦ @'Tensor j2 j1'@, etc.).
type family BraidIrrep (e :: IrrepExpr) :: IrrepExpr where
  BraidIrrep ('Atom j) = 'Atom j
  BraidIrrep ('Tensor j1 j2) = 'Tensor j2 j1

type family BraidMult (μ :: MultExpr) :: MultExpr where
  BraidMult ('AtomM m) = 'AtomM m
  BraidMult ('Prod m n) = 'Prod n m

type family BraidSector (s :: Sector) :: Sector where
  BraidSector '(e, μ) = '(BraidIrrep e, BraidMult μ)

-- | Braid every sector in a spine (@Braid (Tensor r s)@ swaps each distributed pair).
type family Braid (rs :: Rep) :: Rep where
  Braid '[] = '[]
  Braid (s ': rs) = BraidSector s ': Braid rs

--------------------------------------------------------------------------------
-- Multiplicity evaluation / merge
--------------------------------------------------------------------------------

-- | Dimension of a multiplicity expression.
type family EvalMult (μ :: MultExpr) :: Nat where
  EvalMult ('AtomM m) = m
  EvalMult ('Prod m n) = m * n

-- | Same-key merge: always an @'AtomM@ of summed dimensions.
type family AddMult (μ1 :: MultExpr) (μ2 :: MultExpr) :: MultExpr where
  AddMult μ1 μ2 = 'AtomM (EvalMult μ1 + EvalMult μ2)

--------------------------------------------------------------------------------
-- Coalesce: sort + merge sectors with equal 'IrrepExpr'
--------------------------------------------------------------------------------

-- | Total order on irrep expressions (@'Atom' < 'Tensor'@; then lex on labels).
type family CmpIrrep (a :: IrrepExpr) (b :: IrrepExpr) :: Ordering where
  CmpIrrep ('Atom j) ('Atom k) = CmpNat j k
  CmpIrrep ('Atom _) ('Tensor _ _) = 'LT
  CmpIrrep ('Tensor _ _) ('Atom _) = 'GT
  CmpIrrep ('Tensor j1 j2) ('Tensor k1 k2) = CmpIrrepTensor (CmpNat j1 k1) j2 k2

type family CmpIrrepTensor (o :: Ordering) (j2 :: Nat) (k2 :: Nat) :: Ordering where
  CmpIrrepTensor 'EQ j2 k2 = CmpNat j2 k2
  CmpIrrepTensor o _ _ = o

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
type family ToVSector (e :: IrrepExpr) (μ :: MultExpr) :: Type where
  ToVSector ('Atom j) ('AtomM m) = C m ⊗ C (IrrepDim j)
  ToVSector ('Atom j) ('Prod m n) = (C m ⊗ C n) ⊗ C (IrrepDim j)
  ToVSector ('Tensor j1 j2) ('AtomM m) =
    C m ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2)
  ToVSector ('Tensor j1 j2) ('Prod m n) =
    (C m ⊗ C (IrrepDim j1)) ⊗ (C n ⊗ C (IrrepDim j2))

--------------------------------------------------------------------------------
-- Fusion: CG on irreps, then coalesced rep
--------------------------------------------------------------------------------

-- | Tag every CG channel with unit multiplicity (irrep-only fuse).
type family AtomsFromCG (cg :: [(Nat, Nat)]) :: Rep where
  AtomsFromCG '[] = '[]
  AtomsFromCG ('(j, _) ': rest) = '( 'Atom j, 'AtomM 1) ': AtomsFromCG rest

-- | Fuse one 'IrrepExpr' to a 'Rep' of atoms (@'AtomM 1@ on each channel).
type family FuseIrrep (e :: IrrepExpr) :: Rep where
  FuseIrrep ('Atom j) = '[ '( 'Atom j, 'AtomM 1)]
  FuseIrrep ('Tensor j1 j2) = AtomsFromCG (TensorIrrepRepSU2 j1 j2)

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

-- | Distribute: tensor product of two atom-only reps (leaf × leaf).
type family TensorPair (s1 :: Sector) (s2 :: Sector) :: Sector where
  TensorPair '( 'Atom j1, 'AtomM m) '( 'Atom j2, 'AtomM n) =
    '( 'Tensor j1 j2, 'Prod m n)

type family TensorOne (s :: Sector) (q :: Rep) :: Rep where
  TensorOne _ '[] = '[]
  TensorOne s (s2 ': rest) =
    Append '[TensorPair s s2] (TensorOne s rest)

type family Tensor (r :: Rep) (q :: Rep) :: Rep where
  Tensor '[] _ = '[]
  Tensor (s ': rs) q = Append (TensorOne s q) (Tensor rs q)

--------------------------------------------------------------------------------
-- Term-level spine ('RepV') and fusion
--------------------------------------------------------------------------------

-- | Spine of sectors, indexed by type-level 'Rep' (shape-tagged constructors).
data RepV (rs :: Rep) where
  RNil :: RepV '[]

  RConsAtomAtomM
    :: ToVSector ('Atom j) ('AtomM m)
    -> RepV rest
    -> RepV ('( 'Atom j, 'AtomM m) ': rest)

  RConsAtomProd
    :: ToVSector ('Atom j) ('Prod m n)
    -> RepV rest
    -> RepV ('( 'Atom j, 'Prod m n) ': rest)

  RConsTensorAtomM
    :: ToVSector ('Tensor j1 j2) ('AtomM m)
    -> RepV rest
    -> RepV ('( 'Tensor j1 j2, 'AtomM m) ': rest)

  RConsTensorProd
    :: ToVSector ('Tensor j1 j2) ('Prod m n)
    -> RepV rest
    -> RepV ('( 'Tensor j1 j2, 'Prod m n) ': rest)

-- | Pick the matching constructor for @ToVSector e μ@ (coalesce / insert only).
class RepCons (e :: IrrepExpr) (μ :: MultExpr) where
  repCons :: ToVSector e μ -> RepV rest -> RepV ('(e, μ) ': rest)

instance RepCons ('Atom j) ('AtomM m) where
  repCons v rs = RConsAtomAtomM v rs

instance RepCons ('Atom j) ('Prod m n) where
  repCons v rs = RConsAtomProd v rs

instance RepCons ('Tensor j1 j2) ('AtomM m) where
  repCons v rs = RConsTensorAtomM v rs

instance RepCons ('Tensor j1 j2) ('Prod m n) where
  repCons v rs = RConsTensorProd v rs

-- | Link @'Rep'@ to fuse / coalesce on the term-level spine.
class KnownSymbolicRep (rs :: Rep) where
  fuseRaw :: RepV rs -> RepV (FuseRepRaw rs)
  coalesce :: RepV rs -> RepV (Coalesce rs)

instance KnownSymbolicRep '[] where
  fuseRaw RNil = RNil
  coalesce RNil = RNil

instance
  ( KnownSymbolicRep rest
  , FuseOneSector ('Atom j) ('AtomM m)
  , InsertSpine ('Atom j) ('AtomM m) (Coalesce rest)
  ) =>
  KnownSymbolicRep ('( 'Atom j, 'AtomM m) ': rest)
  where
  fuseRaw (RConsAtomAtomM sv rs) =
    appendRepV (fuseOneSector @('Atom j) @('AtomM m) sv) (fuseRaw rs)
  coalesce (RConsAtomAtomM sv rs) =
    insertSpine @('Atom j) @('AtomM m) sv (coalesce rs)

instance
  ( KnownSymbolicRep rest
  , FuseOneSector ('Atom j) ('Prod m n)
  , InsertSpine ('Atom j) ('Prod m n) (Coalesce rest)
  ) =>
  KnownSymbolicRep ('( 'Atom j, 'Prod m n) ': rest)
  where
  fuseRaw (RConsAtomProd sv rs) =
    appendRepV (fuseOneSector @('Atom j) @('Prod m n) sv) (fuseRaw rs)
  coalesce (RConsAtomProd sv rs) =
    insertSpine @('Atom j) @('Prod m n) sv (coalesce rs)

instance
  ( KnownSymbolicRep rest
  , FuseOneSector ('Tensor j1 j2) ('AtomM m)
  , InsertSpine ('Tensor j1 j2) ('AtomM m) (Coalesce rest)
  ) =>
  KnownSymbolicRep ('( 'Tensor j1 j2, 'AtomM m) ': rest)
  where
  fuseRaw (RConsTensorAtomM sv rs) =
    appendRepV (fuseOneSector @('Tensor j1 j2) @('AtomM m) sv) (fuseRaw rs)
  coalesce (RConsTensorAtomM sv rs) =
    insertSpine @('Tensor j1 j2) @('AtomM m) sv (coalesce rs)

instance
  ( KnownSymbolicRep rest
  , FuseOneSector ('Tensor j1 j2) ('Prod m n)
  , InsertSpine ('Tensor j1 j2) ('Prod m n) (Coalesce rest)
  ) =>
  KnownSymbolicRep ('( 'Tensor j1 j2, 'Prod m n) ': rest)
  where
  fuseRaw (RConsTensorProd sv rs) =
    appendRepV (fuseOneSector @('Tensor j1 j2) @('Prod m n) sv) (fuseRaw rs)
  coalesce (RConsTensorProd sv rs) =
    insertSpine @('Tensor j1 j2) @('Prod m n) sv (coalesce rs)

-- | Append two spines (@'Append'@ on keys).
appendRepV
  :: RepV rs1
  -> RepV rs2
  -> RepV (Append rs1 rs2)
appendRepV RNil r2 = r2
appendRepV (RConsAtomAtomM v rest) r2 =
  RConsAtomAtomM v (appendRepV rest r2)
appendRepV (RConsAtomProd v rest) r2 =
  RConsAtomProd v (appendRepV rest r2)
appendRepV (RConsTensorAtomM v rest) r2 =
  RConsTensorAtomM v (appendRepV rest r2)
appendRepV (RConsTensorProd v rest) r2 =
  RConsTensorProd v (appendRepV rest r2)

-- | CG-fuse one sector to a (possibly longer) atom spine.
class FuseOneSector (e :: IrrepExpr) (μ :: MultExpr) where
  fuseOneSector :: ToVSector e μ -> RepV (FuseSector '(e, μ))

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim j)
  , FuseSector '( 'Atom j, 'AtomM m) ~ '[ '( 'Atom j, 'AtomM m)]
  ) =>
  FuseOneSector ('Atom j) ('AtomM m)
  where
  fuseOneSector v = RConsAtomAtomM v RNil

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim j)
  , FuseSector ('( 'Atom j, 'Prod m n)) ~ '[ '( 'Atom j, 'Prod m n)]
  ) =>
  FuseOneSector ('Atom j) ('Prod m n)
  where
  fuseOneSector v = RConsAtomProd v RNil

-- | CG one channel on irrep legs, preserving sector copy layout.
class FuseOneChannel (j1 :: Nat) (j2 :: Nat) (j :: Nat) (μ :: MultExpr) where
  fuseOneChannel :: ToVSector ('Tensor j1 j2) μ -> ToVSector ('Atom j) μ

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat j
  , KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  , KnownNat (IrrepDim j)
  , KnownNat (m * n)
  , LSpace (C m)
  , LSpace (C n)
  , LSpace (C (IrrepDim j1))
  , LSpace (C (IrrepDim j2))
  , LSpace (C (IrrepDim j))
  , LSpace (C m ⊗ C (IrrepDim j1))
  , LSpace (C n ⊗ C (IrrepDim j2))
  , LSpace (C m ⊗ C n)
  , LSpace (C (IrrepDim j1) ⊗ C (IrrepDim j2))
  , LSpace (C m ⊗ C n ⊗ C (IrrepDim j))
  , LSpace ((C m ⊗ C (IrrepDim j1)) ⊗ (C n ⊗ C (IrrepDim j2)))
  , LSpace (C (m * n) ⊗ (C (IrrepDim j1) ⊗ C (IrrepDim j2)))
  , LSpace ((C m ⊗ C n) ⊗ (C (IrrepDim j1) ⊗ C (IrrepDim j2)))
  , LSpace ((C m ⊗ C n) ⊗ C (IrrepDim j))
  , TensorSpace ((C m ⊗ C (IrrepDim j1)) ⊗ (C n ⊗ C (IrrepDim j2)))
  , TensorSpace (C (m * n) ⊗ (C (IrrepDim j1) ⊗ C (IrrepDim j2)))
  , TensorSpace ((C m ⊗ C n) ⊗ (C (IrrepDim j1) ⊗ C (IrrepDim j2)))
  , TensorSpace ((C m ⊗ C n) ⊗ C (IrrepDim j))
  , Scalar (C m) ~ Complex Double
  , Scalar (C n) ~ Complex Double
  , Scalar (C (IrrepDim j1)) ~ Complex Double
  , Scalar (C (IrrepDim j2)) ~ Complex Double
  , Scalar (C (IrrepDim j)) ~ Complex Double
  , Scalar ((C m ⊗ C (IrrepDim j1)) ⊗ (C n ⊗ C (IrrepDim j2))) ~ Complex Double
  , Scalar (C (m * n) ⊗ (C (IrrepDim j1) ⊗ C (IrrepDim j2))) ~ Complex Double
  , Scalar ((C m ⊗ C n) ⊗ (C (IrrepDim j1) ⊗ C (IrrepDim j2))) ~ Complex Double
  , Scalar ((C m ⊗ C n) ⊗ C (IrrepDim j)) ~ Complex Double
  ) =>
  FuseOneChannel j1 j2 j ('Prod m n)
  where
  fuseOneChannel sec =
    ( (id ⊗^ fuseCGChannel @j1 @j2 @j)
        . (splitBond @m @n ⊗^ id)
        . arr (LinearFunction flattenTensorProdCopy)
    )
      $ sec

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  , KnownNat (IrrepDim j)
  , KnownNat (m * n)
  , LSpace (C m)
  , LSpace (C (IrrepDim j1))
  , LSpace (C (IrrepDim j2))
  , LSpace (C (IrrepDim j))
  , LSpace (C m ⊗ C (IrrepDim j1))
  , LSpace (C m ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2))
  , LSpace (C m ⊗ C (IrrepDim j))
  , LSpace ((C m ⊗ C (IrrepDim j1)) ⊗ C (IrrepDim j2))
  , TensorSpace (C m ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2))
  , TensorSpace ((C m ⊗ C (IrrepDim j1)) ⊗ C (IrrepDim j2))
  , TensorSpace (C m ⊗ C (IrrepDim j))
  , Scalar (C m) ~ Complex Double
  , Scalar (C (IrrepDim j1)) ~ Complex Double
  , Scalar (C (IrrepDim j2)) ~ Complex Double
  , Scalar (C (IrrepDim j)) ~ Complex Double
  , Scalar (C m ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2)) ~ Complex Double
  , Scalar ((C m ⊗ C (IrrepDim j1)) ⊗ C (IrrepDim j2)) ~ Complex Double
  , Scalar (C m ⊗ C (IrrepDim j)) ~ Complex Double
  ) =>
  FuseOneChannel j1 j2 j ('AtomM m)
  where
  fuseOneChannel sec =
    ((id ⊗^ fuseCGChannel @j1 @j2 @j) . rassocMap) $ sec

-- | Append one fused atom sector onto a CG spine.
class AppendFusedAtom (j :: Nat) (μ :: MultExpr) (rest :: Rep) where
  appendFusedAtom
    :: ToVSector ('Atom j) μ
    -> RepV rest
    -> RepV ('( 'Atom j, μ) ': rest)

instance AppendFusedAtom j ('AtomM m) rest where
  appendFusedAtom v rest = RConsAtomAtomM v rest

instance AppendFusedAtom j ('Prod m n) rest where
  appendFusedAtom v rest = RConsAtomProd v rest

-- | Walk 'TensorIrrepRepSU2' channels, building a tagged atom spine.
class FuseTensorSpine (j1 :: Nat) (j2 :: Nat) (μ :: MultExpr) (cg :: [(Nat, Nat)]) where
  fuseTensorSpine
    :: ToVSector ('Tensor j1 j2) μ
    -> RepV (TagMult μ (AtomsFromCG cg))

instance FuseTensorSpine j1 j2 μ '[] where
  fuseTensorSpine _ = RNil

instance
  ( FuseTensorSpine j1 j2 μ rest
  , KnownNat j
  , FuseOneChannel j1 j2 j μ
  , AppendFusedAtom j μ (TagMult μ (AtomsFromCG rest))
  ) =>
  FuseTensorSpine j1 j2 μ ('(j, m) ': rest)
  where
  fuseTensorSpine v =
    appendFusedAtom @j @μ (fuseOneChannel @j1 @j2 @j @μ v) (fuseTensorSpine @j1 @j2 @μ @rest v)

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m
  , FuseTensorSpine j1 j2 ('AtomM m) (TensorIrrepRepSU2 j1 j2)
  ) =>
  FuseOneSector ('Tensor j1 j2) ('AtomM m)
  where
  fuseOneSector = fuseTensorSpine @j1 @j2 @('AtomM m) @(TensorIrrepRepSU2 j1 j2)

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m
  , KnownNat n
  , FuseTensorSpine j1 j2 ('Prod m n) (TensorIrrepRepSU2 j1 j2)
  ) =>
  FuseOneSector ('Tensor j1 j2) ('Prod m n)
  where
  fuseOneSector = fuseTensorSpine @j1 @j2 @('Prod m n) @(TensorIrrepRepSU2 j1 j2)

-- | Insert one sector into a coalesced spine (sort + merge on equal keys).
class InsertSpine (e :: IrrepExpr) (μ :: MultExpr) (rs :: Rep) where
  insertSpine
    :: ToVSector e μ
    -> RepV rs
    -> RepV (InsertSector e μ rs)

instance RepCons e μ => InsertSpine e μ '[] where
  insertSpine sv RNil = repCons @e @μ sv RNil

instance
  ( RepCons e μ
  , CmpIrrep e ('Atom j) ~ ord
  , InsertCompared ord e μ ('Atom j) ('AtomM m) rest
  ) =>
  InsertSpine e μ ('( 'Atom j, 'AtomM m) ': rest)
  where
  insertSpine sv (RConsAtomAtomM sv2 restR) =
    insertCompared @ord @e @μ @('Atom j) @('AtomM m) sv sv2 restR

instance
  ( RepCons e μ
  , CmpIrrep e ('Atom j) ~ ord
  , InsertCompared ord e μ ('Atom j) ('Prod m n) rest
  ) =>
  InsertSpine e μ ('( 'Atom j, 'Prod m n) ': rest)
  where
  insertSpine sv (RConsAtomProd sv2 restR) =
    insertCompared @ord @e @μ @('Atom j) @('Prod m n) sv sv2 restR

instance
  ( RepCons e μ
  , CmpIrrep e ('Tensor j1 j2) ~ ord
  , InsertCompared ord e μ ('Tensor j1 j2) ('AtomM m) rest
  ) =>
  InsertSpine e μ ('( 'Tensor j1 j2, 'AtomM m) ': rest)
  where
  insertSpine sv (RConsTensorAtomM sv2 restR) =
    insertCompared @ord @e @μ @('Tensor j1 j2) @('AtomM m) sv sv2 restR

instance
  ( RepCons e μ
  , CmpIrrep e ('Tensor j1 j2) ~ ord
  , InsertCompared ord e μ ('Tensor j1 j2) ('Prod m n) rest
  ) =>
  InsertSpine e μ ('( 'Tensor j1 j2, 'Prod m n) ': rest)
  where
  insertSpine sv (RConsTensorProd sv2 restR) =
    insertCompared @ord @e @μ @('Tensor j1 j2) @('Prod m n) sv sv2 restR

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

class MergeSector (j :: Nat) (μ1 :: MultExpr) (μ2 :: MultExpr) (μOut :: MultExpr) where
  mergeSector
    :: ToVSector ('Atom j) μ1
    -> ToVSector ('Atom j) μ2
    -> ToVSector ('Atom j) μOut

instance
  ( KnownNat j
  , KnownNat m1
  , KnownNat m2
  , KnownNat mOut
  , mOut ~ m1 + m2
  , KnownNat (IrrepDim j)
  , LSpace (C m1)
  , LSpace (C m2)
  , LSpace (C mOut)
  , LSpace (C (IrrepDim j))
  , LSpace (C m1 ⊗ C (IrrepDim j))
  , LSpace (C m2 ⊗ C (IrrepDim j))
  , LSpace (C mOut ⊗ C (IrrepDim j))
  , TensorSpace (C m1 ⊗ C (IrrepDim j))
  , TensorSpace (C m2 ⊗ C (IrrepDim j))
  , TensorSpace (C mOut ⊗ C (IrrepDim j))
  , Scalar (C m1) ~ Complex Double
  , Scalar (C m2) ~ Complex Double
  , Scalar (C (IrrepDim j)) ~ Complex Double
  ) =>
  MergeSector j ('AtomM m1) ('AtomM m2) ('AtomM mOut)
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
  , LSpace (C m1)
  , LSpace (C n1)
  , LSpace (C m2)
  , LSpace (C n2)
  , LSpace (C ma)
  , LSpace (C mb)
  , LSpace (C mOut)
  , LSpace (C (IrrepDim j))
  , LSpace (C m1 ⊗ C n1)
  , LSpace (C m2 ⊗ C n2)
  , LSpace ((C m1 ⊗ C n1) ⊗ C (IrrepDim j))
  , LSpace ((C m2 ⊗ C n2) ⊗ C (IrrepDim j))
  , LSpace (C ma ⊗ C (IrrepDim j))
  , LSpace (C mb ⊗ C (IrrepDim j))
  , LSpace (C mOut ⊗ C (IrrepDim j))
  , TensorSpace (C m1 ⊗ C n1)
  , TensorSpace (C m2 ⊗ C n2)
  , TensorSpace (C ma)
  , TensorSpace (C mb)
  , TensorSpace ((C m1 ⊗ C n1) ⊗ C (IrrepDim j))
  , TensorSpace ((C m2 ⊗ C n2) ⊗ C (IrrepDim j))
  , TensorSpace (C ma ⊗ C (IrrepDim j))
  , TensorSpace (C mb ⊗ C (IrrepDim j))
  , TensorSpace (C mOut ⊗ C (IrrepDim j))
  , Scalar (C m1) ~ Complex Double
  , Scalar (C n1) ~ Complex Double
  , Scalar (C m2) ~ Complex Double
  , Scalar (C n2) ~ Complex Double
  , Scalar (C (IrrepDim j)) ~ Complex Double
  ) =>
  MergeSector j ('Prod m1 n1) ('Prod m2 n2) ('AtomM mOut)
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
  , LSpace (C m1)
  , LSpace (C m2)
  , LSpace (C n2)
  , LSpace (C mb)
  , LSpace (C mOut)
  , LSpace (C (IrrepDim j))
  , LSpace (C m2 ⊗ C n2)
  , LSpace (C m1 ⊗ C (IrrepDim j))
  , LSpace ((C m2 ⊗ C n2) ⊗ C (IrrepDim j))
  , LSpace (C mb ⊗ C (IrrepDim j))
  , LSpace (C mOut ⊗ C (IrrepDim j))
  , TensorSpace (C m2 ⊗ C n2)
  , TensorSpace (C mb)
  , TensorSpace ((C m2 ⊗ C n2) ⊗ C (IrrepDim j))
  , TensorSpace (C m1 ⊗ C (IrrepDim j))
  , TensorSpace (C mb ⊗ C (IrrepDim j))
  , TensorSpace (C mOut ⊗ C (IrrepDim j))
  , Scalar (C m1) ~ Complex Double
  , Scalar (C m2) ~ Complex Double
  , Scalar (C n2) ~ Complex Double
  , Scalar (C (IrrepDim j)) ~ Complex Double
  ) =>
  MergeSector j ('AtomM m1) ('Prod m2 n2) ('AtomM mOut)
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
  , LSpace (C m1)
  , LSpace (C n1)
  , LSpace (C m2)
  , LSpace (C ma)
  , LSpace (C mOut)
  , LSpace (C (IrrepDim j))
  , LSpace (C m1 ⊗ C n1)
  , LSpace ((C m1 ⊗ C n1) ⊗ C (IrrepDim j))
  , LSpace (C m2 ⊗ C (IrrepDim j))
  , LSpace (C ma ⊗ C (IrrepDim j))
  , LSpace (C mOut ⊗ C (IrrepDim j))
  , TensorSpace (C m1 ⊗ C n1)
  , TensorSpace (C ma)
  , TensorSpace ((C m1 ⊗ C n1) ⊗ C (IrrepDim j))
  , TensorSpace (C m2 ⊗ C (IrrepDim j))
  , TensorSpace (C ma ⊗ C (IrrepDim j))
  , TensorSpace (C mOut ⊗ C (IrrepDim j))
  , Scalar (C m1) ~ Complex Double
  , Scalar (C n1) ~ Complex Double
  , Scalar (C m2) ~ Complex Double
  , Scalar (C (IrrepDim j)) ~ Complex Double
  ) =>
  MergeSector j ('Prod m1 n1) ('AtomM m2) ('AtomM mOut)
  where
  mergeSector v1 v2 =
    mergeCopyAxis @ma @m2 @(IrrepDim j)
      (flattenCopyProd @m1 @n1 @(IrrepDim j) v1)
      v2

class MergeTensorSector
  (j1 :: Nat) (j2 :: Nat) (μ1 :: MultExpr) (μ2 :: MultExpr) (μOut :: MultExpr)
 where
  mergeTensorSector
    :: ToVSector ('Tensor j1 j2) μ1
    -> ToVSector ('Tensor j1 j2) μ2
    -> ToVSector ('Tensor j1 j2) μOut

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m1
  , KnownNat m2
  , KnownNat mOut
  , mOut ~ m1 + m2
  , KnownNat (IrrepDim j1)
  , KnownNat (IrrepDim j2)
  , LSpace (C m1)
  , LSpace (C m2)
  , LSpace (C mOut)
  , LSpace (C (IrrepDim j1))
  , LSpace (C (IrrepDim j2))
  , LSpace (C (IrrepDim j1) ⊗ C (IrrepDim j2))
  , LSpace (C m1 ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2))
  , LSpace (C m2 ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2))
  , LSpace (C mOut ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2))
  , TensorSpace (C (IrrepDim j1) ⊗ C (IrrepDim j2))
  , TensorSpace (C m1 ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2))
  , TensorSpace (C m2 ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2))
  , TensorSpace (C mOut ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2))
  , Scalar (C m1) ~ Complex Double
  , Scalar (C m2) ~ Complex Double
  , Scalar (C (IrrepDim j1)) ~ Complex Double
  , Scalar (C (IrrepDim j2)) ~ Complex Double
  ) =>
  MergeTensorSector j1 j2 ('AtomM m1) ('AtomM m2) ('AtomM mOut)
  where
  mergeTensorSector v1 v2 =
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
  , LSpace (C m1)
  , LSpace (C n1)
  , LSpace (C m2)
  , LSpace (C n2)
  , LSpace (C ma)
  , LSpace (C mb)
  , LSpace (C mOut)
  , LSpace (C (IrrepDim j1))
  , LSpace (C (IrrepDim j2))
  , LSpace (C m1 ⊗ C (IrrepDim j1))
  , LSpace (C n1 ⊗ C (IrrepDim j2))
  , LSpace (C m2 ⊗ C (IrrepDim j1))
  , LSpace (C n2 ⊗ C (IrrepDim j2))
  , LSpace ((C m1 ⊗ C (IrrepDim j1)) ⊗ (C n1 ⊗ C (IrrepDim j2)))
  , LSpace ((C m2 ⊗ C (IrrepDim j1)) ⊗ (C n2 ⊗ C (IrrepDim j2)))
  , LSpace (C (IrrepDim j1) ⊗ C (IrrepDim j2))
  , LSpace (C ma ⊗ (C (IrrepDim j1) ⊗ C (IrrepDim j2)))
  , LSpace (C mb ⊗ (C (IrrepDim j1) ⊗ C (IrrepDim j2)))
  , LSpace (C mOut ⊗ (C (IrrepDim j1) ⊗ C (IrrepDim j2)))
  , TensorSpace ((C m1 ⊗ C (IrrepDim j1)) ⊗ (C n1 ⊗ C (IrrepDim j2)))
  , TensorSpace ((C m2 ⊗ C (IrrepDim j1)) ⊗ (C n2 ⊗ C (IrrepDim j2)))
  , TensorSpace (C (IrrepDim j1) ⊗ C (IrrepDim j2))
  , TensorSpace (C ma ⊗ (C (IrrepDim j1) ⊗ C (IrrepDim j2)))
  , TensorSpace (C mb ⊗ (C (IrrepDim j1) ⊗ C (IrrepDim j2)))
  , TensorSpace (C mOut ⊗ (C (IrrepDim j1) ⊗ C (IrrepDim j2)))
  , Scalar (C m1) ~ Complex Double
  , Scalar (C n1) ~ Complex Double
  , Scalar (C m2) ~ Complex Double
  , Scalar (C n2) ~ Complex Double
  , Scalar (C (IrrepDim j1)) ~ Complex Double
  , Scalar (C (IrrepDim j2)) ~ Complex Double
  ) =>
  MergeTensorSector j1 j2 ('Prod m1 n1) ('Prod m2 n2) ('AtomM mOut)
  where
  mergeTensorSector v1 v2 =
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
  , LSpace (C m1)
  , LSpace (C m2)
  , LSpace (C n2)
  , LSpace (C mb)
  , LSpace (C mOut)
  , LSpace (C (IrrepDim j1))
  , LSpace (C (IrrepDim j2))
  , LSpace (C m2 ⊗ C (IrrepDim j1))
  , LSpace (C n2 ⊗ C (IrrepDim j2))
  , LSpace ((C m2 ⊗ C (IrrepDim j1)) ⊗ (C n2 ⊗ C (IrrepDim j2)))
  , LSpace (C m1 ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2))
  , LSpace (C (IrrepDim j1) ⊗ C (IrrepDim j2))
  , LSpace (C mb ⊗ (C (IrrepDim j1) ⊗ C (IrrepDim j2)))
  , LSpace (C mOut ⊗ (C (IrrepDim j1) ⊗ C (IrrepDim j2)))
  , TensorSpace ((C m2 ⊗ C (IrrepDim j1)) ⊗ (C n2 ⊗ C (IrrepDim j2)))
  , TensorSpace (C (IrrepDim j1) ⊗ C (IrrepDim j2))
  , TensorSpace (C m1 ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2))
  , TensorSpace (C mb ⊗ (C (IrrepDim j1) ⊗ C (IrrepDim j2)))
  , TensorSpace (C mOut ⊗ (C (IrrepDim j1) ⊗ C (IrrepDim j2)))
  , Scalar (C m1) ~ Complex Double
  , Scalar (C m2) ~ Complex Double
  , Scalar (C n2) ~ Complex Double
  , Scalar (C (IrrepDim j1)) ~ Complex Double
  , Scalar (C (IrrepDim j2)) ~ Complex Double
  ) =>
  MergeTensorSector j1 j2 ('AtomM m1) ('Prod m2 n2) ('AtomM mOut)
  where
  mergeTensorSector v1 v2 =
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
  , LSpace (C m1)
  , LSpace (C n1)
  , LSpace (C m2)
  , LSpace (C ma)
  , LSpace (C mOut)
  , LSpace (C (IrrepDim j1))
  , LSpace (C (IrrepDim j2))
  , LSpace (C m1 ⊗ C (IrrepDim j1))
  , LSpace (C n1 ⊗ C (IrrepDim j2))
  , LSpace ((C m1 ⊗ C (IrrepDim j1)) ⊗ (C n1 ⊗ C (IrrepDim j2)))
  , LSpace (C m2 ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2))
  , LSpace (C (IrrepDim j1) ⊗ C (IrrepDim j2))
  , LSpace (C ma ⊗ (C (IrrepDim j1) ⊗ C (IrrepDim j2)))
  , LSpace (C mOut ⊗ (C (IrrepDim j1) ⊗ C (IrrepDim j2)))
  , TensorSpace ((C m1 ⊗ C (IrrepDim j1)) ⊗ (C n1 ⊗ C (IrrepDim j2)))
  , TensorSpace (C (IrrepDim j1) ⊗ C (IrrepDim j2))
  , TensorSpace (C m2 ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2))
  , TensorSpace (C ma ⊗ (C (IrrepDim j1) ⊗ C (IrrepDim j2)))
  , TensorSpace (C mOut ⊗ (C (IrrepDim j1) ⊗ C (IrrepDim j2)))
  , Scalar (C m1) ~ Complex Double
  , Scalar (C n1) ~ Complex Double
  , Scalar (C m2) ~ Complex Double
  , Scalar (C (IrrepDim j1)) ~ Complex Double
  , Scalar (C (IrrepDim j2)) ~ Complex Double
  ) =>
  MergeTensorSector j1 j2 ('Prod m1 n1) ('AtomM m2) ('AtomM mOut)
  where
  mergeTensorSector v1 v2 =
    mergeCopyAxisTensorLeft @ma @m2 @(IrrepDim j1) @(IrrepDim j2)
      (tensorProdLeft (flattenTensorProdCopy @m1 @n1 @(IrrepDim j1) @(IrrepDim j2) v1))
      v2

instance
  ( j ~ k
  , AddMult μ μ2 ~ μOut
  , MergeSector j μ μ2 μOut
  ) =>
  InsertCompared 'EQ ('Atom j) μ ('Atom k) μ2 rest
  where
  insertCompared sv sv2 restR =
    RConsAtomAtomM (mergeSector @j @μ @μ2 @μOut sv sv2) restR

instance
  ( RepCons ('Atom j) μ
  , RepCons ('Atom k) μ2
  ) =>
  InsertCompared 'LT ('Atom j) μ ('Atom k) μ2 rest
  where
  insertCompared sv sv2 restR =
    repCons @('Atom j) @μ sv (repCons @('Atom k) @μ2 sv2 restR)

instance
  ( KnownSymbolicRep rest
  , InsertSpine ('Atom j) μ rest
  , RepCons ('Atom k) μ2
  ) =>
  InsertCompared 'GT ('Atom j) μ ('Atom k) μ2 rest
  where
  insertCompared sv sv2 restR =
    repCons @('Atom k) @μ2 sv2 (insertSpine @('Atom j) @μ sv restR)

instance
  ( RepCons ('Atom j) μ
  , RepCons ('Tensor k1 k2) μ2
  ) =>
  InsertCompared 'LT ('Atom j) μ ('Tensor k1 k2) μ2 rest
  where
  insertCompared sv sv2 restR =
    repCons @('Atom j) @μ sv (repCons @('Tensor k1 k2) @μ2 sv2 restR)

instance
  ( KnownSymbolicRep rest
  , InsertSpine ('Tensor j1 j2) μ rest
  , RepCons ('Atom k) μ2
  ) =>
  InsertCompared 'GT ('Tensor j1 j2) μ ('Atom k) μ2 rest
  where
  insertCompared sv sv2 restR =
    repCons @('Atom k) @μ2 sv2 (insertSpine @('Tensor j1 j2) @μ sv restR)

instance
  ( RepCons ('Tensor j1 j2) μ
  , RepCons ('Tensor k1 k2) μ2
  ) =>
  InsertCompared 'LT ('Tensor j1 j2) μ ('Tensor k1 k2) μ2 rest
  where
  insertCompared sv sv2 restR =
    repCons @('Tensor j1 j2) @μ
      sv
      (repCons @('Tensor k1 k2) @μ2 sv2 restR)

instance
  ( KnownSymbolicRep rest
  , InsertSpine ('Tensor j1 j2) μ rest
  , RepCons ('Tensor k1 k2) μ2
  ) =>
  InsertCompared 'GT ('Tensor j1 j2) μ ('Tensor k1 k2) μ2 rest
  where
  insertCompared sv sv2 restR =
    repCons @('Tensor k1 k2) @μ2
      sv2
      (insertSpine @('Tensor j1 j2) @μ sv restR)

instance
  ( j1 ~ k1
  , j2 ~ k2
  , AddMult μ μ2 ~ μOut
  , MergeTensorSector j1 j2 μ μ2 μOut
  ) =>
  InsertCompared 'EQ ('Tensor j1 j2) μ ('Tensor k1 k2) μ2 rest
  where
  insertCompared sv sv2 restR =
    RConsTensorAtomM
      (mergeTensorSector @j1 @j2 @μ @μ2 @μOut sv sv2)
      restR

-- | CG fuse every sector, append, coalesce.
fuse
  :: forall rs
   . ( KnownSymbolicRep rs
     , KnownSymbolicRep (FuseRepRaw rs)
     , KnownSymbolicRep (Fuse rs)
     )
  => RepV rs
  -> RepV (Fuse rs)
fuse rv =
  coalesce @(FuseRepRaw rs) (fuseRaw rv)

-- | CG fuse a distributed tensor rep (@'Tensor'@).
fuseTensor
  :: forall r s
   . ( KnownSymbolicRep (Tensor r s)
     , KnownSymbolicRep (FuseRepRaw (Tensor r s))
     , KnownSymbolicRep (Fuse (Tensor r s))
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
     , Tensor
         '[ '( 'Atom j1, 'AtomM m1)]
         '[ '( 'Atom j2, 'AtomM m2)]
         ~ '[ '( 'Tensor j1 j2, 'Prod m1 m2)]
     )
  => C m1 ⊗ C (IrrepDim j1)
  -> C m2 ⊗ C (IrrepDim j2)
  -> RepV
       ( Tensor
           '[ '( 'Atom j1, 'AtomM m1)]
           '[ '( 'Atom j2, 'AtomM m2)]
       )
tensorAtoms s1 s2 = RConsTensorProd (s1 ⊗ s2) RNil

-- | Categorical swap of copy factors @C m ⊗ C n@ (irrep leg unchanged).
swapCopyProductSector
  :: forall m n d
   . ( KnownNat m
     , KnownNat n
     , KnownNat d
     , LSpace (C m)
     , LSpace (C n)
     , LSpace (C d)
     , LSpace (C m ⊗ C n)
     , LSpace (C n ⊗ C m)
     , LSpace (C m ⊗ C n ⊗ C d)
     , LSpace (C n ⊗ C m ⊗ C d)
     , TensorSpace (C m ⊗ C n ⊗ C d)
     , Scalar (C m) ~ Complex Double
     , Scalar (C n) ~ Complex Double
     , Scalar (C d) ~ Complex Double
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
     , LSpace (C m)
     , LSpace (C (IrrepDim j1))
     , LSpace (C (IrrepDim j2))
     , LSpace (C m ⊗ C (IrrepDim j1))
     , LSpace (C m ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2))
     , LSpace (C m ⊗ C (IrrepDim j2) ⊗ C (IrrepDim j1))
     , LSpace ((C m ⊗ C (IrrepDim j1)) ⊗ C (IrrepDim j2))
     , LSpace ((C m ⊗ C (IrrepDim j2)) ⊗ C (IrrepDim j1))
     , LSpace (C m ⊗ (C (IrrepDim j1) ⊗ C (IrrepDim j2)))
     , LSpace (C m ⊗ (C (IrrepDim j2) ⊗ C (IrrepDim j1)))
     , TensorSpace ((C m ⊗ C (IrrepDim j1)) ⊗ C (IrrepDim j2))
     , Scalar (C m) ~ Complex Double
     , Scalar (C (IrrepDim j1)) ~ Complex Double
     , Scalar (C (IrrepDim j2)) ~ Complex Double
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
     , LSpace (C m)
     , LSpace (C n)
     , LSpace (C (IrrepDim j1))
     , LSpace (C (IrrepDim j2))
     , LSpace (C m ⊗ C (IrrepDim j1))
     , LSpace (C n ⊗ C (IrrepDim j2))
     , LSpace ((C m ⊗ C (IrrepDim j1)) ⊗ (C n ⊗ C (IrrepDim j2)))
     , LSpace ((C n ⊗ C (IrrepDim j2)) ⊗ (C m ⊗ C (IrrepDim j1)))
     , TensorSpace ((C m ⊗ C (IrrepDim j1)) ⊗ (C n ⊗ C (IrrepDim j2)))
     , Scalar (C m) ~ Complex Double
     , Scalar (C n) ~ Complex Double
     , Scalar (C (IrrepDim j1)) ~ Complex Double
     , Scalar (C (IrrepDim j2)) ~ Complex Double
     )
  => (C m ⊗ C (IrrepDim j1)) ⊗ (C n ⊗ C (IrrepDim j2))
  -> (C n ⊗ C (IrrepDim j2)) ⊗ (C m ⊗ C (IrrepDim j1))
swapTensorProductSector sec = swapMap $ sec

-- | Constraints for braiding every sector in a spine.
type family BraidSpine (rs :: Rep) :: Constraint where
  BraidSpine '[] = ()
  BraidSpine ('( 'Atom j, 'AtomM m) ': rest) =
    ( KnownNat j
    , KnownNat m
    , KnownNat (IrrepDim j)
    , Scalar (ToVSector ('Atom j) ('AtomM m)) ~ Complex Double
    , BraidSpine rest
    )
  BraidSpine ('( 'Atom j, 'Prod m n) ': rest) =
    ( KnownNat j
    , KnownNat m
    , KnownNat n
    , KnownNat (IrrepDim j)
    , LSpace (C m)
    , LSpace (C n)
    , LSpace (C (IrrepDim j))
    , LSpace (C m ⊗ C n)
    , LSpace (C n ⊗ C m)
    , LSpace (C m ⊗ C n ⊗ C (IrrepDim j))
    , LSpace (C n ⊗ C m ⊗ C (IrrepDim j))
    , TensorSpace (C m ⊗ C n ⊗ C (IrrepDim j))
    , Scalar (C m) ~ Complex Double
    , Scalar (C n) ~ Complex Double
    , Scalar (C (IrrepDim j)) ~ Complex Double
    , ToVSector ('Atom j) ('Prod m n) ~ (C m ⊗ C n) ⊗ C (IrrepDim j)
    , BraidSpine rest
    )
  BraidSpine ('( 'Tensor j1 j2, 'AtomM m) ': rest) =
    ( KnownNat j1
    , KnownNat j2
    , KnownNat m
    , KnownNat (IrrepDim j1)
    , KnownNat (IrrepDim j2)
    , LSpace (C m)
    , LSpace (C (IrrepDim j1))
    , LSpace (C (IrrepDim j2))
    , LSpace (C m ⊗ C (IrrepDim j1))
    , LSpace (C m ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2))
    , LSpace (C m ⊗ C (IrrepDim j2))
    , LSpace (C m ⊗ C (IrrepDim j2) ⊗ C (IrrepDim j1))
    , TensorSpace (C m ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2))
    , Scalar (C m) ~ Complex Double
    , Scalar (C (IrrepDim j1)) ~ Complex Double
    , Scalar (C (IrrepDim j2)) ~ Complex Double
    , ToVSector ('Tensor j1 j2) ('AtomM m)
        ~ C m ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2)
    , BraidSpine rest
    )
  BraidSpine ('( 'Tensor j1 j2, 'Prod m n) ': rest) =
    ( KnownNat j1
    , KnownNat j2
    , KnownNat m
    , KnownNat n
    , KnownNat (IrrepDim j1)
    , KnownNat (IrrepDim j2)
    , LSpace (C m)
    , LSpace (C n)
    , LSpace (C (IrrepDim j1))
    , LSpace (C (IrrepDim j2))
    , LSpace (C m ⊗ C (IrrepDim j1))
    , LSpace (C n ⊗ C (IrrepDim j2))
    , LSpace ((C m ⊗ C (IrrepDim j1)) ⊗ (C n ⊗ C (IrrepDim j2)))
    , LSpace ((C n ⊗ C (IrrepDim j2)) ⊗ (C m ⊗ C (IrrepDim j1)))
    , TensorSpace ((C m ⊗ C (IrrepDim j1)) ⊗ (C n ⊗ C (IrrepDim j2)))
    , Scalar (C m) ~ Complex Double
    , Scalar (C n) ~ Complex Double
    , Scalar (C (IrrepDim j1)) ~ Complex Double
    , Scalar (C (IrrepDim j2)) ~ Complex Double
    , ToVSector ('Tensor j1 j2) ('Prod m n)
        ~ (C m ⊗ C (IrrepDim j1)) ⊗ (C n ⊗ C (IrrepDim j2))
    , BraidSpine rest
    )

-- | Project a spine onto its trivial (@'Atom 0@) sectors.
--
-- A class is required: @RepV@ existentials do not refine @j ~ 0@, and
-- 'FilterTrivial' will not reduce on a skolem @j@. Keep vs drop is
-- @CmpNat j 0@-dispatched ('ProjectAtomOrd'), same pattern as 'InsertCompared'.
class ProjectToSymmetric (rs :: Rep) where
  projectToSymmetric :: RepV rs -> RepV (FilterTrivial rs)

instance ProjectToSymmetric '[] where
  projectToSymmetric RNil = RNil

instance
  ( CmpNat j 0 ~ ord
  , ProjectAtomOrd ord j ('AtomM m) rest
  ) =>
  ProjectToSymmetric ('( 'Atom j, 'AtomM m) ': rest)
  where
  projectToSymmetric (RConsAtomAtomM v rs) =
    projectAtomOrd @ord @j @('AtomM m) v rs

instance
  ( CmpNat j 0 ~ ord
  , ProjectAtomOrd ord j ('Prod m n) rest
  ) =>
  ProjectToSymmetric ('( 'Atom j, 'Prod m n) ': rest)
  where
  projectToSymmetric (RConsAtomProd v rs) =
    projectAtomOrd @ord @j @('Prod m n) v rs

instance
  ( FilterTrivial ('( 'Tensor j1 j2, 'AtomM m) ': rest) ~ FilterTrivial rest
  , ProjectToSymmetric rest
  ) =>
  ProjectToSymmetric ('( 'Tensor j1 j2, 'AtomM m) ': rest)
  where
  projectToSymmetric (RConsTensorAtomM _ rs) = projectToSymmetric rs

instance
  ( FilterTrivial ('( 'Tensor j1 j2, 'Prod m n) ': rest) ~ FilterTrivial rest
  , ProjectToSymmetric rest
  ) =>
  ProjectToSymmetric ('( 'Tensor j1 j2, 'Prod m n) ': rest)
  where
  projectToSymmetric (RConsTensorProd _ rs) = projectToSymmetric rs

-- | Keep (@'EQ@ / @j ~ 0@) or drop (@'GT@) an atom sector under 'FilterTrivial'.
class ProjectAtomOrd
  (ord :: Ordering)
  (j :: Nat)
  (μ :: MultExpr)
  (rest :: Rep)
 where
  projectAtomOrd
    :: ToVSector ('Atom j) μ
    -> RepV rest
    -> RepV (FilterTrivial ('( 'Atom j, μ) ': rest))

instance
  ( j ~ 0
  , ProjectToSymmetric rest
  , RepCons ('Atom 0) μ
  ) =>
  ProjectAtomOrd 'EQ j μ rest
  where
  projectAtomOrd v rs =
    repCons @('Atom 0) @μ v (projectToSymmetric rs)

instance
  ( FilterTrivial ('( 'Atom j, μ) ': rest) ~ FilterTrivial rest
  , ProjectToSymmetric rest
  ) =>
  ProjectAtomOrd 'GT j μ rest
  where
  projectAtomOrd _ rs = projectToSymmetric rs

-- | Braid every sector in a 'RepV' spine.
braid
  :: forall rs
   . BraidSpine rs
  => RepV rs
  -> RepV (Braid rs)
braid RNil = RNil
braid (RConsAtomAtomM @j @m v rs) = RConsAtomAtomM v (braid rs)
braid (RConsAtomProd @j @m @n v rs) =
  RConsAtomProd (swapCopyProductSector @m @n @(IrrepDim j) v) (braid rs)
braid (RConsTensorAtomM @j1 @j2 @m v rs) =
  RConsTensorAtomM (swapIrrepTensorSector @m @j1 @j2 v) (braid rs)
braid (RConsTensorProd @j1 @j2 @m @n v rs) =
  RConsTensorProd (swapTensorProductSector @m @n @j1 @j2 v) (braid rs)

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

-- | Fused spine after R-move: @'Prod m n'@ copy legs swap to @'Prod n m'@.
type family RmoveTarget (j1 :: Nat) (j2 :: Nat) (rs :: Rep) :: Rep where
  RmoveTarget j1 j2 '[] = '[]
  RmoveTarget j1 j2 ('( 'Atom j, 'AtomM m) ': rest) =
    '( 'Atom j, 'AtomM m) ': RmoveTarget j1 j2 rest
  RmoveTarget j1 j2 ('( 'Atom j, 'Prod m n) ': rest) =
    '( 'Atom j, 'Prod n m) ': RmoveTarget j1 j2 rest
  RmoveTarget j1 j2 ('( 'Tensor j1' j2', 'AtomM m) ': rest) =
    '( 'Tensor j1' j2', 'AtomM m) ': RmoveTarget j1 j2 rest
  RmoveTarget j1 j2 ('( 'Tensor j1' j2', 'Prod m n) ': rest) =
    '( 'Tensor j1' j2', 'Prod n m) ': RmoveTarget j1 j2 rest

-- | Constraints for R-moving every sector in a fused spine.
type family RmoveSpine (j1 :: Nat) (j2 :: Nat) (rs :: Rep) :: Constraint where
  RmoveSpine j1 j2 '[] = ()
  RmoveSpine j1 j2 ('( 'Atom j, 'AtomM m) ': rest) =
    ( KnownNat j1
    , KnownNat j2
    , KnownNat j
    , KnownNat m
    , KnownNat (IrrepDim j)
    , VectorSpace (ToVSector ('Atom j) ('AtomM m))
    , Scalar (ToVSector ('Atom j) ('AtomM m)) ~ Complex Double
    , RmoveSpine j1 j2 rest
    )
  RmoveSpine j1 j2 ('( 'Atom j, 'Prod m n) ': rest) =
    ( KnownNat j1
    , KnownNat j2
    , KnownNat j
    , KnownNat m
    , KnownNat n
    , KnownNat (IrrepDim j)
    , VectorSpace (ToVSector ('Atom j) ('Prod m n))
    , Scalar (ToVSector ('Atom j) ('Prod m n)) ~ Complex Double
    , LSpace (C m)
    , LSpace (C n)
    , LSpace (C (IrrepDim j))
    , LSpace (C m ⊗ C n)
    , LSpace (C n ⊗ C m)
    , LSpace (C m ⊗ C n ⊗ C (IrrepDim j))
    , LSpace (C n ⊗ C m ⊗ C (IrrepDim j))
    , TensorSpace (C m ⊗ C n ⊗ C (IrrepDim j))
    , Scalar (C m) ~ Complex Double
    , Scalar (C n) ~ Complex Double
    , Scalar (C (IrrepDim j)) ~ Complex Double
    , ToVSector ('Atom j) ('Prod m n) ~ (C m ⊗ C n) ⊗ C (IrrepDim j)
    , RmoveSpine j1 j2 rest
    )

-- | R-move every sector in a fused 'RepV' spine (R-phase, then copy swap on @'Prod'@).
rmoveSpine
  :: forall j1 j2 rs
   . RmoveSpine j1 j2 rs
  => RepV rs
  -> RepV (RmoveTarget j1 j2 rs)
rmoveSpine RNil = RNil
rmoveSpine (RConsAtomAtomM @j @m v rs) =
  RConsAtomAtomM (rPhaseSector @j1 @j2 @j @('AtomM m) v) (rmoveSpine @j1 @j2 rs)
rmoveSpine (RConsAtomProd @j @m @n v rs) =
  RConsAtomProd
    ( swapCopyProductSector @m @n @(IrrepDim j)
        (rPhaseSector @j1 @j2 @j @('Prod m n) v)
    )
    (rmoveSpine @j1 @j2 rs)

-- Fused spines should not retain unfused @'Tensor'@ heads; keep total.
rmoveSpine (RConsTensorAtomM _ _) =
  error "rmoveSpine: fused spine should not contain Tensor sectors"
rmoveSpine (RConsTensorProd _ _) =
  error "rmoveSpine: fused spine should not contain Tensor sectors"

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
  '( 'Tensor 1 2
   , 'Prod 3 5
   )

type SmokeRep = '[SmokeSector]

type SmokeBraidSector =
  AssertEqSector
    (BraidSector SmokeSector)
    '( 'Tensor 2 1
     , 'Prod 5 3
     )

type SmokeBraid =
  AssertEqRep
    (Braid SmokeRep)
    '[ '( 'Tensor 2 1
        , 'Prod 5 3
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
    '[ '( 'Tensor 2 1, 'Prod 3 2)]

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
      '[ '( 'Tensor 1 2, 'Prod 2 3)
       , '( 'Tensor 1 2, 'Prod 1 4)
       ])
    '[ '( 'Tensor 1 2, 'AtomM 10)]

-- | Distinct keys stay sorted (@'Atom' < 'Tensor'@).
type SmokeCoalesceSort =
  AssertEqRep
    (Coalesce
      '[ '( 'Tensor 0 1, 'AtomM 1)
       , '( 'Atom 2, 'AtomM 1)
       ])
    '[ '( 'Atom 2, 'AtomM 1)
     , '( 'Tensor 0 1, 'AtomM 1)
     ]

-- | Leaf sector @('Atom 1, 'AtomM 3)@ → @C 3 ⊗ C 2@.
type SmokeSectorAtom =
  AssertEqType
    (ToVSector ('Atom 1) ('AtomM 3))
    (C 3 ⊗ C 2)

type SmokeSectorTensor =
  AssertEqType
    (ToVSector ('Tensor 1 2) ('Prod 2 3))
    ((C 2 ⊗ C 2) ⊗ (C 3 ⊗ C 3))

-- | @1 ⊗ 2@ (SU2) → @j = 1, 3@ channels.
type SmokeFuseIrrep =
  AssertEqRep
    (FuseIrrep ('Tensor 1 2))
    '[ '( 'Atom 1, 'AtomM 1)
     , '( 'Atom 3, 'AtomM 1)
     ]

-- | Sector fuse tags copy multiplicity onto each CG channel.
type SmokeFuseSector =
  AssertEqRep
    (FuseSector '( 'Tensor 1 2, 'Prod 2 3))
    '[ '( 'Atom 1, 'Prod 2 3)
     , '( 'Atom 3, 'Prod 2 3)
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
    '[ '( 'Atom 1, 'Prod 2 3)
     , '( 'Atom 3, 'Prod 2 3)
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
    '[ '( 'Atom 1, 'Prod 3 2)
     , '( 'Atom 3, 'Prod 3 2)
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
        (TagMult ('AtomM 6) (FuseIrrep ('Tensor 2 1)))
    )
    ( Coalesce
        (TagMult ('AtomM 6) (FuseIrrep ('Tensor 1 2)))
    )

-- | Reference flat fuse layout for @1 ⊗ 2@, @m = 2@, @n = 3@.
type SmokeFusedLeaf12 =
  AssertEqRep
    (Coalesce (TagMult ('AtomM 6) (FuseIrrep ('Tensor 1 2))))
    '[ '( 'Atom 1, 'AtomM 6)
     , '( 'Atom 3, 'AtomM 6)
     ]

-- | 'FilterTrivial' keeps only @'Atom 0@ sectors.
type SmokeFilterTrivial =
  AssertEqRep
    ( FilterTrivial
        '[ '( 'Atom 1, 'AtomM 2)
         , '( 'Atom 0, 'AtomM 3)
         , '( 'Tensor 1 1, 'Prod 1 1)
         , '( 'Atom 0, 'Prod 2 2)
         ]
    )
    '[ '( 'Atom 0, 'AtomM 3)
     , '( 'Atom 0, 'Prod 2 2)
     ]

-- | 'RepV' spine type is stable under its own index.
type SmokeRepVSpine =
  AssertEqType
    (RepV '[ '( 'Atom 1, 'AtomM 2), '( 'Tensor 0 1, 'AtomM 1)])
    (RepV '[ '( 'Atom 1, 'AtomM 2), '( 'Tensor 0 1, 'AtomM 1)])

smokeBraidSector :: Proxy SmokeBraidSector
smokeBraidSector = Proxy

smokeBraid :: Proxy SmokeBraid
smokeBraid = Proxy

smokeBraidTensor :: Proxy SmokeBraidTensor
smokeBraidTensor = Proxy

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
