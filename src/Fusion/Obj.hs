{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

-- | Theory-parameterized fusion trees: @Norm@, @Fuse@, @Mult@ from @FuseN@.
--
-- @Stabilize@ \/ @Mults@ \/ @Mult@-on-@:⊗:@ walk @Irr t@, so they are for
-- 'FiniteIrr' theories only (Fib, Ising, …). Unbounded Nat labels (SU(2)) use
-- 'ObjSpine' instead: FuseNorm → CollectSimples → coalesced 'Spine'.
-- Rigid duals: 'DualObj' (via 'DualLab'); no @'Dual@ constructor on 'Obj'.
module Fusion.Obj
  ( Obj (..)
  , FlattenSum
  , Norm
  , DualObj
  , Fuse
  , FuseNorm
  , FuseTensor
  , CollectSimples
  , Stabilize
  , Mult
  , Mults
  , NOf
  , FuseIdemMult
  , HomDim
  , ObjSpine
  , ObjSpineZ
  ) where

import Data.Kind (Constraint, Type)
import Data.Type.Bool (If)
import Data.Type.Equality (type (==))
import Fusion.Theory (FiniteIrr (..), FusionTheory (..))
import Fusion.Unbounded (Spine)
import GHC.TypeLits (CmpNat, Nat, type (*), type (+), type (-))
import Symmetry.Utils (Z)
import Symmetry.Tensor (CmpZ)

--------------------------------------------------------------------------------
-- Trees
--------------------------------------------------------------------------------

-- | Formal objects: simples (@'Irrep@), tensor (@':⊗:'@), binary sums (@':⊕:'@).
data Obj lab
  = Irrep lab
  | Obj lab :⊗: Obj lab
  | Obj lab :⊕: Obj lab

--------------------------------------------------------------------------------
-- Dual (rigid rewrite; no 'Dual' constructor)
--------------------------------------------------------------------------------

-- | Dual object: @('Irrep j)^* = 'Irrep (DualLab t j)@, reverse tensors,
-- distribute over sums. Eliminates duals rather than storing a @'Dual@ node.
type family DualObj (t :: Type) (a :: Obj lab) :: Obj lab where
  DualObj t ('Irrep j) = 'Irrep (DualLab t j)
  DualObj t ((a :⊗: b)) = ((DualObj t b) :⊗: (DualObj t a))
  DualObj t ((a :⊕: b)) = ((DualObj t a) :⊕: (DualObj t b))

--------------------------------------------------------------------------------
-- Norm
--------------------------------------------------------------------------------

type family FlattenSum (a :: Obj lab) (b :: Obj lab) :: Obj lab where
  FlattenSum ((a :⊕: b)) c = FlattenSum a (FlattenSum b c)
  FlattenSum a ((b :⊕: c)) = (a :⊕: (FlattenSum b c))
  FlattenSum a b = (a :⊕: b)

-- | Distribute @⊗@ over @⊕@, right-flatten sums. Does /not/ apply @FuseN@.
type family Norm (a :: Obj lab) :: Obj lab where
  Norm ('Irrep s) = 'Irrep s
  Norm ((((a :⊕: b)) :⊗: c)) = Norm ((((a :⊗: c)) :⊕: ((b :⊗: c))))
  Norm ((a :⊗: ((b :⊕: c)))) = Norm ((((a :⊗: b)) :⊕: ((a :⊗: c))))
  Norm ((a :⊗: b)) = ((Norm a) :⊗: (Norm b))
  Norm ((((a :⊕: b)) :⊕: c)) = Norm ((a :⊕: ((b :⊕: c))))
  Norm ((a :⊕: b)) = FlattenSum (Norm a) (Norm b)

--------------------------------------------------------------------------------
-- FuseN → object
--------------------------------------------------------------------------------

-- | Multiplicity of charge @c@ in @FuseN@ list.
type family NOf (t :: Type) (a :: lab) (b :: lab) (c :: lab) :: Nat where
  NOf t a b c = NOfList c (FuseN t a b)

type family NOfList (c :: lab) (xs :: [(lab, Nat)]) :: Nat where
  NOfList _ '[] = 0
  NOfList c ('(c, n) ': _rest) = n
  NOfList c ('(_d, _n) ': rest) = NOfList c rest

type family ReplicateObj (n :: Nat) (a :: Obj lab) :: Obj lab where
  ReplicateObj 1 a = a
  ReplicateObj n a = (a :⊕: (ReplicateObj (n - 1) a))

-- | Expand @FuseN@ entries to a right-nested sum of irreps (duplicates = multiplicity).
type family IrrepsFromN (ns :: [(lab, Nat)]) :: Obj lab where
  IrrepsFromN '[ '(s, n)] = ReplicateObj n ('Irrep s)
  IrrepsFromN ('(s, n) ': rest) =
    FlattenSum (ReplicateObj n ('Irrep s)) (IrrepsFromN rest)

--------------------------------------------------------------------------------
-- Fuse
--------------------------------------------------------------------------------

type family FuseLeft
  (t :: Type)
  (u :: lab)
  (b :: Obj lab)
  (isUnit :: Bool) :: Obj lab where
  FuseLeft _t _u b 'True = b
  FuseLeft t u ('Irrep b) 'False = IrrepsFromN (FuseN t u b)
  FuseLeft t u b 'False = FuseNorm t (Norm ((('Irrep u) :⊗: b)))

type family FuseRight
  (t :: Type)
  (a :: Obj lab)
  (u :: lab)
  (isUnit :: Bool) :: Obj lab where
  FuseRight _t a _u 'True = a
  FuseRight t ('Irrep a) u 'False = IrrepsFromN (FuseN t a u)
  FuseRight t a u 'False = FuseNorm t (Norm ((a :⊗: ('Irrep u))))

type family FuseTensorPair (t :: Type) (a :: Obj lab) (b :: Obj lab) :: Obj lab where
  FuseTensorPair t ('Irrep u) b =
    FuseLeft t u b (u == UnitLab t)
  FuseTensorPair t a ('Irrep u) =
    FuseRight t a u (u == UnitLab t)
  FuseTensorPair t a b = FuseNorm t (Norm ((a :⊗: b)))

-- | Fuse a tensor tree using @FuseN@ \/ unitors, then re-@Norm@.
type family FuseTensor (t :: Type) (a :: Obj lab) :: Obj lab where
  FuseTensor _t ('Irrep s) = 'Irrep s
  FuseTensor t ((a :⊕: b)) = FlattenSum (FuseTensor t a) (FuseTensor t b)
  FuseTensor t ((a :⊗: b)) =
    FuseTensorPair t (FuseTensor t a) (FuseTensor t b)

type family FuseNorm (t :: Type) (a :: Obj lab) :: Obj lab where
  FuseNorm _t ('Irrep s) = 'Irrep s
  FuseNorm t ((a :⊗: b)) = FuseTensor t ((a :⊗: b))
  FuseNorm t ((a :⊕: b)) = FlattenSum (FuseNorm t a) (FuseNorm t b)

--------------------------------------------------------------------------------
-- Stabilize (Irr order)
--------------------------------------------------------------------------------

type family AppendObj (xs :: [Obj lab]) (ys :: [Obj lab]) :: [Obj lab] where
  AppendObj '[] ys = ys
  AppendObj (x ': xs) ys = x ': AppendObj xs ys

type family CollectSimples (t :: Type) (a :: Obj lab) :: [Obj lab] where
  CollectSimples _t ('Irrep s) = '[ 'Irrep s]
  CollectSimples t ((a :⊕: b)) =
    AppendObj (CollectSimples t a) (CollectSimples t b)
  CollectSimples t ((a :⊗: b)) =
    CollectSimples t (FuseTensor t ((a :⊗: b)))

type family FilterLab (s :: lab) (xs :: [Obj lab]) :: [Obj lab] where
  FilterLab _s '[] = '[]
  FilterLab s ('Irrep s ': xs) = 'Irrep s ': FilterLab s xs
  FilterLab s ('Irrep _t ': xs) = FilterLab s xs
  FilterLab s (_x ': xs) = FilterLab s xs

type family SortByIrr (irr :: [lab]) (xs :: [Obj lab]) :: [Obj lab] where
  SortByIrr '[] _xs = '[]
  SortByIrr (s ': ss) xs = AppendObj (FilterLab s xs) (SortByIrr ss xs)

type family SpineFrom (xs :: [Obj lab]) :: Obj lab where
  SpineFrom '[x] = x
  SpineFrom (x ': y ': ys) = (x :⊕: (SpineFrom (y ': ys)))

type family Stabilize (t :: Type) (a :: Obj lab) :: Obj lab where
  Stabilize t a = SpineFrom (SortByIrr (Irr t) (CollectSimples t a))

type family Fuse (t :: Type) (a :: Obj lab) :: Obj lab where
  Fuse t a = Stabilize t (FuseNorm t (Norm a))

--------------------------------------------------------------------------------
-- Obj → Spine (unbounded Nat labels; no Irr walk)
--------------------------------------------------------------------------------

-- | Semisimplicity map for @Obj Nat@: FuseNorm, collect irreps, coalesce into a
-- sorted finite-support 'Spine' (@(2j, multiplicity)@). Safe for SU(2) \/ U(1)
-- where @Stabilize@ cannot walk a complete @Irr@.
type family ObjSpine (t :: Type) (a :: Obj Nat) :: Spine Nat where
  ObjSpine t a = CoalesceNatIrreps (CollectSimples t (FuseNorm t (Norm a)))

-- | Insertion-sort coalesce of @'Irrep@ lists into @Spine Nat@.
type family CoalesceNatIrreps (xs :: [Obj Nat]) :: Spine Nat where
  CoalesceNatIrreps '[] = '[]
  CoalesceNatIrreps ('Irrep j ': rest) =
    SpineInsertNat j 1 (CoalesceNatIrreps rest)

type family SpineInsertNat (j :: Nat) (n :: Nat) (sp :: Spine Nat) :: Spine Nat where
  SpineInsertNat j n '[] = '[ '(j, n)]
  SpineInsertNat j n ('(k, m) ': rest) =
    SpineInsertNatOrd (CmpNat j k) j n k m rest

type family SpineInsertNatOrd
  (o :: Ordering)
  (j :: Nat)
  (n :: Nat)
  (k :: Nat)
  (m :: Nat)
  (rest :: Spine Nat)
  :: Spine Nat
  where
  SpineInsertNatOrd 'EQ j n _k m rest = '(j, n + m) ': rest
  SpineInsertNatOrd 'LT j n k m rest = '(j, n) ': '(k, m) ': rest
  SpineInsertNatOrd 'GT j n k m rest = '(k, m) ': SpineInsertNat j n rest

--------------------------------------------------------------------------------
-- Obj → Spine (unbounded Z charges; U(1))
--------------------------------------------------------------------------------

-- | Semisimplicity map for @Obj Z@: FuseNorm → collect → coalesced 'Spine Z'.
type family ObjSpineZ (t :: Type) (a :: Obj Z) :: Spine Z where
  ObjSpineZ t a = CoalesceZIrreps (CollectSimples t (FuseNorm t (Norm a)))

type family CoalesceZIrreps (xs :: [Obj Z]) :: Spine Z where
  CoalesceZIrreps '[] = '[]
  CoalesceZIrreps ('Irrep j ': rest) =
    SpineInsertZ j 1 (CoalesceZIrreps rest)

type family SpineInsertZ (j :: Z) (n :: Nat) (sp :: Spine Z) :: Spine Z where
  SpineInsertZ j n '[] = '[ '(j, n)]
  SpineInsertZ j n ('(k, m) ': rest) =
    SpineInsertZOrd (CmpZ j k) j n k m rest

type family SpineInsertZOrd
  (o :: Ordering)
  (j :: Z)
  (n :: Nat)
  (k :: Z)
  (m :: Nat)
  (rest :: Spine Z)
  :: Spine Z
  where
  SpineInsertZOrd 'EQ j n _k m rest = '(j, n + m) ': rest
  SpineInsertZOrd 'LT j n k m rest = '(j, n) ': '(k, m) ': rest
  SpineInsertZOrd 'GT j n k m rest = '(k, m) ': SpineInsertZ j n rest

--------------------------------------------------------------------------------
-- Multiplicities
--------------------------------------------------------------------------------

type DeltaLab (s :: lab) (r :: lab) = If (s == r) 1 0

-- | @n_s(X)@: multiplicity of simple @s@ in object @X@.
type family Mult (t :: Type) (s :: lab) (a :: Obj lab) :: Nat where
  Mult _t s ('Irrep r) = DeltaLab s r
  Mult t s (a :⊕: b ) = Mult t s a + Mult t s b
  Mult t s (a :⊗: b) = MultTensor t s a b (Irr t)

type family MultTensor
  (t :: Type)
  (c :: lab)
  (a :: Obj lab)
  (b :: Obj lab)
  (xs :: [lab]) :: Nat where
  MultTensor _t _c _a _b '[] = 0
  MultTensor t c a b (x ': xs) =
    MultTensorY t c a b x (Irr t) + MultTensor t c a b xs

type family MultTensorY
  (t :: Type)
  (c :: lab)
  (a :: Obj lab)
  (b :: Obj lab)
  (x :: lab)
  (ys :: [lab]) :: Nat where
  MultTensorY _t _c _a _b _x '[] = 0
  MultTensorY t c a b x (y ': ys) =
    Mult t x a * Mult t y b * NOf t x y c
      + MultTensorY t c a b x ys

-- | Multiplicity vector aligned with @Irr t@.
type family Mults (t :: Type) (a :: Obj lab) :: [Nat] where
  Mults t a = MultsOver t a (Irr t)

type family MultsOver (t :: Type) (a :: Obj lab) (xs :: [lab]) :: [Nat] where
  MultsOver _t _a '[] = '[]
  MultsOver t a (s ': ss) = Mult t s a ': MultsOver t a ss

type family HomDim (t :: Type) (a :: Obj lab) (b :: Obj lab) :: Nat where
  HomDim t a b = HomDimZip (Mults t a) (Mults t b)

type family HomDimZip (xs :: [Nat]) (ys :: [Nat]) :: Nat where
  HomDimZip '[] '[] = 0
  HomDimZip (x ': xs) (y ': ys) = x * y + HomDimZip xs ys

type family FuseIdemMult (t :: Type) (a :: Obj lab) :: Constraint where
  FuseIdemMult t a = Mults t a ~ Mults t (Fuse t a)
