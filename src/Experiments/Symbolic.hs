{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

-- | Green-field symbolic SU(2) reps: flat irrep @'Tensor j1 j2@ and flat
-- multiplicity @'Prod m n@.
--
-- Fusion-tree association is temporal (@Fuse@ then tensor again), so tensors
-- are always leaf×leaf. 'Coalesce' merges same-'IrrepExpr' sectors by adding
-- evaluated multiplicities into an @'AtomM@. 'ToV' interprets a 'Rep' as an
-- @'HList'@ of copy @⊗@ irrep sector spaces.
module Experiments.Symbolic where

import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import GHC.TypeLits (CmpNat, Nat, type (*), type (+))
import Math.LinearMap.Category (type (⊗))
import Numeric.LinearAlgebra.Static (C)
import Symmetry.Utils (HList)

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
-- Braid (swap factors)
--------------------------------------------------------------------------------

-- | @Tensor j1 j2 ↦ Tensor j2 j1@; identity on atoms.
type family BraidIrrep (e :: IrrepExpr) :: IrrepExpr where
  BraidIrrep ('Atom j) = 'Atom j
  BraidIrrep ('Tensor j1 j2) = 'Tensor j2 j1

-- | @Prod m n ↦ Prod n m@; identity on atoms.
type family BraidMult (μ :: MultExpr) :: MultExpr where
  BraidMult ('AtomM m) = 'AtomM m
  BraidMult ('Prod m n) = 'Prod n m

type family BraidSector (s :: Sector) :: Sector where
  BraidSector '(e, μ) = '(BraidIrrep e, BraidMult μ)

type family BraidRep (rs :: Rep) :: Rep where
  BraidRep '[] = '[]
  BraidRep (s ': rs) = BraidSector s ': BraidRep rs

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
-- ToV: symbolic rep → concrete sector spaces
--------------------------------------------------------------------------------

-- | SU(2) irrep dimension @j ↦ j + 1@.
type family IrrepDim (j :: Nat) :: Nat where
  IrrepDim j = j + 1

-- | Irrep carrier from an 'IrrepExpr'.
type family ToVIrrep (e :: IrrepExpr) :: Type where
  ToVIrrep ('Atom j) = C (IrrepDim j)
  ToVIrrep ('Tensor j1 j2) = C (IrrepDim j1) ⊗ C (IrrepDim j2)

-- | Copy space from a 'MultExpr' (@'Prod'@ stays factored for braid).
type family ToVMult (μ :: MultExpr) :: Type where
  ToVMult ('AtomM m) = C m
  ToVMult ('Prod m n) = C m ⊗ C n

-- | One sector: copy @⊗@ irrep (same convention as 'Experiments.General').
type family ToVSector (s :: Sector) :: Type where
  ToVSector '(e, μ) = ToVMult μ ⊗ ToVIrrep e

-- | Spine of sector spaces for a 'Rep'.
type family ToVSpine (rs :: Rep) :: [Type] where
  ToVSpine '[] = '[]
  ToVSpine (s ': rs) = ToVSector s ': ToVSpine rs

-- | Interpret a symbolic rep as an @'HList'@ of sector spaces.
type ToV (rs :: Rep) = HList (ToVSpine rs)

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

type SmokeBraidIrrep =
  AssertEqIrrep
    (BraidIrrep ('Tensor 1 2))
    ('Tensor 2 1)

type SmokeBraidMult =
  AssertEqMult
    (BraidMult ('Prod 3 5))
    ('Prod 5 3)

type SmokeSector =
  '( 'Tensor 1 2
   , 'Prod 3 5
   )

type SmokeBraidSector =
  AssertEqSector
    (BraidSector SmokeSector)
    '( 'Tensor 2 1
     , 'Prod 5 3
     )

type SmokeRep = '[SmokeSector]

type SmokeBraidRep =
  AssertEqRep
    (BraidRep SmokeRep)
    '[ '( 'Tensor 2 1
        , 'Prod 5 3
        )
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
type SmokeToVAtom =
  AssertEqType
    (ToVSector '( 'Atom 1, 'AtomM 3))
    (C 3 ⊗ C 2)

-- | Tensor sector keeps factored copy and irrep legs.
type SmokeToVTensor =
  AssertEqType
    (ToVSector '( 'Tensor 1 2, 'Prod 2 3))
    ((C 2 ⊗ C 3) ⊗ (C 2 ⊗ C 3))

-- | Full rep is an 'HList' spine.
type SmokeToVRep =
  AssertEqType
    (ToV '[ '( 'Atom 1, 'AtomM 2), '( 'Tensor 0 1, 'AtomM 1)])
    (HList '[C 2 ⊗ C 2, C 1 ⊗ (C 1 ⊗ C 2)])

smokeBraidIrrep :: Proxy SmokeBraidIrrep
smokeBraidIrrep = Proxy

smokeBraidMult :: Proxy SmokeBraidMult
smokeBraidMult = Proxy

smokeBraidSector :: Proxy SmokeBraidSector
smokeBraidSector = Proxy

smokeBraidRep :: Proxy SmokeBraidRep
smokeBraidRep = Proxy

smokeCoalesceAtoms :: Proxy SmokeCoalesceAtoms
smokeCoalesceAtoms = Proxy

smokeCoalesceTensors :: Proxy SmokeCoalesceTensors
smokeCoalesceTensors = Proxy

smokeCoalesceSort :: Proxy SmokeCoalesceSort
smokeCoalesceSort = Proxy

smokeToVAtom :: Proxy SmokeToVAtom
smokeToVAtom = Proxy

smokeToVTensor :: Proxy SmokeToVTensor
smokeToVTensor = Proxy

smokeToVRep :: Proxy SmokeToVRep
smokeToVRep = Proxy
