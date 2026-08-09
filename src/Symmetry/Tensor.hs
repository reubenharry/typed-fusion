{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}

-- | Type-level tensor product of representation spines (@Rep g@).
--
-- @'Tensor' g r q@ is the __coalesced__ fused spine: each irrep label appears at
-- most once, multiplicities summed, sectors sorted by irrep label. That is the
-- layout expected by 'IntertwinerG' \/ F-symbols (multiplicity = fusion-channel
-- space). The raw unfused CG branching before coalesce is 'TensorRaw'.
--
-- Runtime fuse maps ('Symmetry.CG.SU2.fuseSU2Flat', U(1) forget) must emit this
-- same coalesced order.
module Symmetry.Tensor
  ( Tensor
  , TensorRaw
  , TensorOne
  , TensorU1
  , TensorIrrepRepSU2
  , Coalesce
  , InsertSector
  ) where

import GHC.TypeLits (Nat, CmpNat, type (+), type (-))
import Symmetry.Group (Group (..), Irreps, Rep)
import Symmetry.Utils (Add, Append, Scale, Z (..))

-- | Fused spine @r ⊗ q@, coalesced and sorted by irrep.
type family Tensor (g :: Group) (r :: Rep g) (q :: Rep g) :: Rep g where
  Tensor g r q = Coalesce g (TensorRaw g r q)

-- | Uncoalesced CG branching (left sectors × right sectors, Append order).
type family TensorRaw (g :: Group) (r :: Rep g) (q :: Rep g) :: Rep g where
  TensorRaw U1 '[] _ = '[]
  TensorRaw U1 ('(i, m) ': rs) q =
    Append (TensorOne U1 '(i, m) q) (TensorRaw U1 rs q)
  TensorRaw SU2 '[] _ = '[]
  TensorRaw SU2 ('(i, m) ': rs) q =
    Append (TensorOne SU2 '(i, m) q) (TensorRaw SU2 rs q)

type family TensorOne (g :: Group) (x :: (Irreps g, Nat)) (q :: Rep g) :: Rep g where
  TensorOne U1 _ '[] = '[]
  TensorOne U1 '(i, m) ('(j, n) ': qs) =
    '(Add i j, Scale m n) ': TensorOne U1 '(i, m) qs
  TensorOne SU2 _ '[] = '[]
  TensorOne SU2 '(i, m) ('(j, n) ': qs) =
    Append
      (ScaleRep (Scale m n) (TensorIrrepRepSU2 i j))
      (TensorOne SU2 '(i, m) qs)

type TensorU1 (r :: Rep U1) (q :: Rep U1) = Tensor U1 r q

--------------------------------------------------------------------------------
-- Coalesce: merge equal irreps, sort by label
--------------------------------------------------------------------------------

-- | Merge duplicate irrep labels (sum multiplicities) and sort.
type family Coalesce (g :: Group) (r :: Rep g) :: Rep g where
  Coalesce U1 r = CoalesceU1 r
  Coalesce SU2 r = CoalesceSU2 r

type family CoalesceU1 (r :: [(Z, Nat)]) :: [(Z, Nat)] where
  CoalesceU1 '[] = '[]
  CoalesceU1 ('(j, m) ': rest) = InsertSectorU1 j m (CoalesceU1 rest)

type family CoalesceSU2 (r :: [(Nat, Nat)]) :: [(Nat, Nat)] where
  CoalesceSU2 '[] = '[]
  CoalesceSU2 ('(j, m) ': rest) = InsertSectorSU2 j m (CoalesceSU2 rest)

-- | Insert into an already-coalesced sorted U(1) spine.
type family InsertSectorU1 (j :: Z) (m :: Nat) (r :: [(Z, Nat)]) :: [(Z, Nat)] where
  InsertSectorU1 j m '[] = '[ '(j, m)]
  InsertSectorU1 j m ('(j2, n) ': rest) =
    InsertSectorZ (CmpZ j j2) j m j2 n rest

-- | Insert into an already-coalesced sorted SU(2) spine.
type family InsertSectorSU2 (j :: Nat) (m :: Nat) (r :: [(Nat, Nat)]) :: [(Nat, Nat)] where
  InsertSectorSU2 j m '[] = '[ '(j, m)]
  InsertSectorSU2 j m ('(j2, n) ': rest) =
    InsertSectorNat (CmpNat j j2) j m j2 n rest

-- | Group-indexed insert (for export / callers that still have @g@).
type family InsertSector (g :: Group) (j :: Irreps g) (m :: Nat) (r :: Rep g) :: Rep g where
  InsertSector U1 j m r = InsertSectorU1 j m r
  InsertSector SU2 j m r = InsertSectorSU2 j m r

type family InsertSectorNat
  (o :: Ordering) (j :: Nat) (m :: Nat) (j2 :: Nat) (n :: Nat) (rest :: [(Nat, Nat)])
  :: [(Nat, Nat)] where
  InsertSectorNat 'EQ j m _ n rest = '(j, m + n) ': rest
  InsertSectorNat 'LT j m j2 n rest = '(j, m) ': '(j2, n) ': rest
  InsertSectorNat 'GT j m j2 n rest = '(j2, n) ': InsertSectorSU2 j m rest

type family InsertSectorZ
  (o :: Ordering) (j :: Z) (m :: Nat) (j2 :: Z) (n :: Nat) (rest :: [(Z, Nat)])
  :: [(Z, Nat)] where
  InsertSectorZ 'EQ j m _ n rest = '(j, m + n) ': rest
  InsertSectorZ 'LT j m j2 n rest = '(j, m) ': '(j2, n) ': rest
  InsertSectorZ 'GT j m j2 n rest = '(j2, n) ': InsertSectorU1 j m rest

-- | Total order on U(1) charges: @Neg@ (more negative first), @Zero@, @Pos@.
type family CmpZ (a :: Z) (b :: Z) :: Ordering where
  CmpZ 'Zero 'Zero = 'EQ
  CmpZ 'Zero ('Pos _) = 'LT
  CmpZ 'Zero ('Neg _) = 'GT
  CmpZ ('Pos _) 'Zero = 'GT
  CmpZ ('Neg _) 'Zero = 'LT
  CmpZ ('Pos a) ('Pos b) = CmpNat a b
  CmpZ ('Neg a) ('Neg b) = CmpNat b a
  CmpZ ('Neg _) ('Pos _) = 'LT
  CmpZ ('Pos _) ('Neg _) = 'GT

--------------------------------------------------------------------------------
-- SU(2) irrep branching
--------------------------------------------------------------------------------

type family TensorIrrepRepSU2 (j1 :: Nat) (j2 :: Nat) :: [(Nat, Nat)] where
  TensorIrrepRepSU2 j1 j2 =
    ToMultiplicityOneList (RangeStep2 (AbsDiff j1 j2) (j1 + j2))

type family ScaleRep (s :: Nat) (xs :: [(Nat, Nat)]) :: [(Nat, Nat)] where
  ScaleRep _ '[] = '[]
  ScaleRep s ('(j, n) ': xs) = '(j, Scale s n) ': ScaleRep s xs

type family ToMultiplicityOneList (js :: [Nat]) :: [(Nat, Nat)] where
  ToMultiplicityOneList '[] = '[]
  ToMultiplicityOneList (j ': js) = '(j, 1) ': ToMultiplicityOneList js

type family AbsDiff (a :: Nat) (b :: Nat) :: Nat where
  AbsDiff a b = AbsDiffCmp (CmpNat a b) a b

type family AbsDiffCmp (o :: Ordering) (a :: Nat) (b :: Nat) :: Nat where
  AbsDiffCmp 'LT a b = b - a
  AbsDiffCmp 'EQ _ _ = 0
  AbsDiffCmp 'GT a b = a - b

type family RangeStep2 (lo :: Nat) (hi :: Nat) :: [Nat] where
  RangeStep2 lo hi = RangeStep2Cmp (CmpNat lo hi) lo hi

type family RangeStep2Cmp (o :: Ordering) (lo :: Nat) (hi :: Nat) :: [Nat] where
  RangeStep2Cmp 'GT _ _ = '[]
  RangeStep2Cmp 'EQ lo _ = '[lo]
  RangeStep2Cmp 'LT lo hi = lo ': RangeStep2 (lo + 2) hi
