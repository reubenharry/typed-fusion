{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

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
-- Tensor CG fuse is not implemented in production here — see
-- 'Experiments.Symbolic.Reference' for the flat @fuseSU2Flat@ oracle.
--
-- Examples: 'Experiments.SymbolicExamples'.
module Experiments.Symbolic where

import Data.Complex (Complex)
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Data.VectorSpace (Scalar)
import GHC.TypeLits (CmpNat, KnownNat, Nat, type (*), type (+))
import Control.Arrow.Constrained (($))
import Control.Category.Constrained.Prelude (Category (..))
import Experiments.SU2 (TensorIrrepRepSU2)
import Math.LinearMap.Category (type (⊗), (⊗), LSpace, TensorSpace)
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.LinearMap.Category.Instances ()
import Numeric.LinearAlgebra.Static (C)
import Symmetry.Utils (Append)
import TensorNetwork.Categorical
  ( flattenCopyProd
  , flattenTensorProdCopy
  , lassocMap
  , mergeCopyAxis
  , mergeCopyAxisTensorLeft
  , rassocMap
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

--------------------------------------------------------------------------------
-- Sector spaces (concrete vectors indexed by irrep / multiplicity)
--------------------------------------------------------------------------------

-- | SU(2) irrep dimension @j ↦ j + 1@.
type family IrrepDim (j :: Nat) :: Nat where
  IrrepDim j = j + 1

-- | Sector space from irrep expression + multiplicity.
type family ToVSectorE (e :: IrrepExpr) (μ :: MultExpr) :: Type where
  ToVSectorE ('Atom j) ('AtomM m) = C m ⊗ C (IrrepDim j)
  ToVSectorE ('Atom j) ('Prod m n) = (C m ⊗ C n) ⊗ C (IrrepDim j)
  ToVSectorE ('Tensor j1 j2) ('AtomM m) =
    C m ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2)
  ToVSectorE ('Tensor j1 j2) ('Prod m n) =
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

-- | One sector, indexed by irrep key and multiplicity.
data SectorV (e :: IrrepExpr) (μ :: MultExpr) where
  SV :: ToVSectorE e μ -> SectorV e μ

-- | Spine of sectors, indexed by type-level 'Rep'.
data RepV (rs :: Rep) where
  RNil :: RepV '[]
  RCons :: SectorV e μ -> RepV rest -> RepV ('(e, μ) ': rest)

-- | Link @'Rep'@ to fuse / coalesce on the term-level spine.
class KnownSymbolicRep (rs :: Rep) where
  fuseRaw :: RepV rs -> RepV (FuseRepRaw rs)
  coalesce :: RepV rs -> RepV (Coalesce rs)

instance KnownSymbolicRep '[] where
  fuseRaw RNil = RNil
  coalesce RNil = RNil

instance
  ( KnownSymbolicRep rest
  , FuseOneSector e μ
  , InsertSpine e μ (Coalesce rest)
  ) =>
  KnownSymbolicRep ('(e, μ) ': rest)
  where
  fuseRaw (RCons sv rs) =
    appendRepV (fuseOneSector sv) (fuseRaw rs)
  coalesce (RCons sv rs) = insertSpine sv (coalesce rs)

-- | Append two spines (@'Append'@ on keys).
appendRepV
  :: RepV rs1
  -> RepV rs2
  -> RepV (Append rs1 rs2)
appendRepV RNil r2 = r2
appendRepV (RCons sv rest) r2 = RCons sv (appendRepV rest r2)

-- | CG-fuse one sector to a (possibly longer) atom spine.
class FuseOneSector (e :: IrrepExpr) (μ :: MultExpr) where
  fuseOneSector :: SectorV e μ -> RepV (FuseSector '(e, μ))

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim j)
  , FuseSector '( 'Atom j, 'AtomM m) ~ '[ '( 'Atom j, 'AtomM m)]
  ) =>
  FuseOneSector ('Atom j) ('AtomM m)
  where
  fuseOneSector (SV v) = RCons (SV v) RNil

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat n
  , KnownNat (IrrepDim j)
  , FuseSector ('( 'Atom j, 'Prod m n)) ~ '[ '( 'Atom j, 'Prod m n)]
  ) =>
  FuseOneSector ('Atom j) ('Prod m n)
  where
  fuseOneSector (SV v) = RCons (SV v) RNil

instance
  ( KnownNat j1
  , KnownNat j2
  , KnownNat m
  , KnownNat n
  , FuseSector '( 'Tensor j1 j2, 'Prod m n) ~ FuseIrrep ('Tensor j1 j2)
  ) =>
  FuseOneSector ('Tensor j1 j2) ('Prod m n)
  where
  fuseOneSector _ =
    undefined
      -- Blocker: typed SU(2) CG fuse on @ToVSectorE@ (no flat buffer).
      -- Oracle: 'Experiments.Symbolic.Reference.fuseOneSectorTensorReference'.

-- | Insert one sector into a coalesced spine (sort + merge on equal keys).
class InsertSpine (e :: IrrepExpr) (μ :: MultExpr) (rs :: Rep) where
  insertSpine
    :: SectorV e μ
    -> RepV rs
    -> RepV (InsertSector e μ rs)

instance InsertSpine e μ '[] where
  insertSpine sv RNil = RCons sv RNil

instance
  ( CmpIrrep e e2 ~ ord
  , InsertCompared ord e μ e2 μ2 rest
  ) =>
  InsertSpine e μ ('(e2, μ2) ': rest)
  where
  insertSpine sv (RCons sv2 restR) = insertCompared @ord sv sv2 restR

-- | Compare incoming sector @e@ against spine head @e2@ (@ord ~ CmpIrrep e e2@).
class InsertCompared
  (ord :: Ordering)
  (e :: IrrepExpr) (μ :: MultExpr)
  (e2 :: IrrepExpr) (μ2 :: MultExpr)
  (rest :: Rep)
 where
  insertCompared
    :: SectorV e μ
    -> SectorV e2 μ2
    -> RepV rest
    -> RepV (InsertSectorOrd ord e μ e2 μ2 rest)

class MergeSector (j :: Nat) (μ1 :: MultExpr) (μ2 :: MultExpr) (μOut :: MultExpr) where
  mergeSector
    :: SectorV ('Atom j) μ1
    -> SectorV ('Atom j) μ2
    -> SectorV ('Atom j) μOut

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
  mergeSector (SV v1) (SV v2) =
    SV (mergeCopyAxis @m1 @m2 @(IrrepDim j) v1 v2)

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
  mergeSector (SV v1) (SV v2) =
    SV
      ( mergeCopyAxis @ma @mb @(IrrepDim j)
          (flattenCopyProd @m1 @n1 @(IrrepDim j) v1)
          (flattenCopyProd @m2 @n2 @(IrrepDim j) v2)
      )

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
  mergeSector (SV v1) (SV v2) =
    SV
      ( mergeCopyAxis @m1 @mb @(IrrepDim j) v1
          (flattenCopyProd @m2 @n2 @(IrrepDim j) v2)
      )

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
  mergeSector (SV v1) (SV v2) =
    SV
      ( mergeCopyAxis @ma @m2 @(IrrepDim j)
          (flattenCopyProd @m1 @n1 @(IrrepDim j) v1)
          v2
      )

class MergeTensorSector
  (j1 :: Nat) (j2 :: Nat) (μ1 :: MultExpr) (μ2 :: MultExpr) (μOut :: MultExpr)
 where
  mergeTensorSector
    :: SectorV ('Tensor j1 j2) μ1
    -> SectorV ('Tensor j1 j2) μ2
    -> SectorV ('Tensor j1 j2) μOut

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
  mergeTensorSector (SV v1) (SV v2) =
    SV (mergeCopyAxisTensorLeft @m1 @m2 @(IrrepDim j1) @(IrrepDim j2) v1 v2)

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
  mergeTensorSector (SV v1) (SV v2) =
    SV
      ( mergeCopyAxisTensorLeft @ma @mb @(IrrepDim j1) @(IrrepDim j2)
          (tensorProdLeft (flattenTensorProdCopy @m1 @n1 @(IrrepDim j1) @(IrrepDim j2) v1))
          (tensorProdLeft (flattenTensorProdCopy @m2 @n2 @(IrrepDim j1) @(IrrepDim j2) v2))
      )

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
  mergeTensorSector (SV v1) (SV v2) =
    SV
      ( mergeCopyAxisTensorLeft @m1 @mb @(IrrepDim j1) @(IrrepDim j2) v1
          (tensorProdLeft (flattenTensorProdCopy @m2 @n2 @(IrrepDim j1) @(IrrepDim j2) v2))
      )

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
  mergeTensorSector (SV v1) (SV v2) =
    SV
      ( mergeCopyAxisTensorLeft @ma @m2 @(IrrepDim j1) @(IrrepDim j2)
          (tensorProdLeft (flattenTensorProdCopy @m1 @n1 @(IrrepDim j1) @(IrrepDim j2) v1))
          v2
      )

instance
  ( j ~ k
  , AddMult μ μ2 ~ μOut
  , MergeSector j μ μ2 μOut
  ) =>
  InsertCompared 'EQ ('Atom j) μ ('Atom k) μ2 rest
  where
  insertCompared sv sv2 restR =
    RCons (mergeSector @j @μ @μ2 @μOut sv sv2) restR

instance InsertCompared 'LT ('Atom j) μ ('Atom k) μ2 rest where
  insertCompared sv sv2 restR = RCons sv (RCons sv2 restR)

instance
  ( KnownSymbolicRep rest
  , InsertSpine ('Atom j) μ rest
  ) =>
  InsertCompared 'GT ('Atom j) μ ('Atom k) μ2 rest
  where
  insertCompared sv sv2 restR = RCons sv2 (insertSpine sv restR)

instance InsertCompared 'LT ('Atom j) μ ('Tensor k1 k2) μ2 rest where
  insertCompared sv sv2 restR = RCons sv (RCons sv2 restR)

instance
  ( KnownSymbolicRep rest
  , InsertSpine ('Tensor j1 j2) μ rest
  ) =>
  InsertCompared 'GT ('Tensor j1 j2) μ ('Atom k) μ2 rest
  where
  insertCompared sv sv2 restR = RCons sv2 (insertSpine sv restR)

instance InsertCompared 'LT ('Tensor j1 j2) μ ('Tensor k1 k2) μ2 rest where
  insertCompared sv sv2 restR = RCons sv (RCons sv2 restR)

instance
  ( KnownSymbolicRep rest
  , InsertSpine ('Tensor j1 j2) μ rest
  ) =>
  InsertCompared 'GT ('Tensor j1 j2) μ ('Tensor k1 k2) μ2 rest
  where
  insertCompared sv sv2 restR = RCons sv2 (insertSpine sv restR)

instance
  ( j1 ~ k1
  , j2 ~ k2
  , AddMult μ μ2 ~ μOut
  , MergeTensorSector j1 j2 μ μ2 μOut
  ) =>
  InsertCompared 'EQ ('Tensor j1 j2) μ ('Tensor k1 k2) μ2 rest
  where
  insertCompared sv sv2 restR =
    RCons (mergeTensorSector @j1 @j2 @μ @μ2 @μOut sv sv2) restR

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
tensorAtoms s1 s2 = RCons (SV (s1 ⊗ s2)) RNil

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

-- | Categorical braid on one sector (@'swapMap'@ / copy swap as appropriate).
class BraidSectorV (e :: IrrepExpr) (μ :: MultExpr) where
  braidSectorV
    :: SectorV e μ
    -> SectorV (BraidIrrep e) (BraidMult μ)

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim j)
  , Scalar (ToVSectorE ('Atom j) ('AtomM m)) ~ Complex Double
  ) =>
  BraidSectorV ('Atom j) ('AtomM m)
  where
  braidSectorV (SV v) = SV v

instance
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
  , ToVSectorE ('Atom j) ('Prod m n) ~ (C m ⊗ C n) ⊗ C (IrrepDim j)
  ) =>
  BraidSectorV ('Atom j) ('Prod m n)
  where
  braidSectorV (SV v) = SV (swapCopyProductSector @m @n @(IrrepDim j) v)

instance
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
  , ToVSectorE ('Tensor j1 j2) ('AtomM m)
      ~ C m ⊗ C (IrrepDim j1) ⊗ C (IrrepDim j2)
  ) =>
  BraidSectorV ('Tensor j1 j2) ('AtomM m)
  where
  braidSectorV (SV v) = SV (swapIrrepTensorSector @m @j1 @j2 v)

instance
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
  , ToVSectorE ('Tensor j1 j2) ('Prod m n)
      ~ (C m ⊗ C (IrrepDim j1)) ⊗ (C n ⊗ C (IrrepDim j2))
  ) =>
  BraidSectorV ('Tensor j1 j2) ('Prod m n)
  where
  braidSectorV (SV v) = SV (swapTensorProductSector @m @n @j1 @j2 v)

class Braidable (rs :: Rep) where
  braid :: RepV rs -> RepV (Braid rs)

instance Braidable '[] where
  braid RNil = RNil

instance
  ( Braidable rest
  , BraidSectorV e μ
  ) =>
  Braidable ('(e, μ) ': rest)
  where
  braid (RCons sv rs) =
    RCons (braidSectorV @e @μ sv) (braid rs)

-- | Braid a distributed tensor rep (@'RepV'@ spine — the concrete @ToVSectorE@ vectors).
braidTensor
  :: forall r s
   . Braidable (Tensor r s)
  => RepV (Tensor r s)
  -> RepV (Braid (Tensor r s))
braidTensor = braid

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
    (ToVSectorE ('Atom 1) ('AtomM 3))
    (C 3 ⊗ C 2)

type SmokeSectorTensor =
  AssertEqType
    (ToVSectorE ('Tensor 1 2) ('Prod 2 3))
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

smokeRepVSpine :: Proxy SmokeRepVSpine
smokeRepVSpine = Proxy
