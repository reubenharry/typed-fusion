{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

-- | Theory-parameterized fusion trees: @Norm@, @Fuse@, @Mult@ from @FuseN@.
--
-- @Stabilize@ \/ @Mults@ \/ @Mult@-on-@Tensor@ walk @Irr t@, so they are for
-- 'FiniteIrr' theories only (Fib, Ising, …).
module Experiments.Fusion.Obj
  ( Obj (..)
  , FlattenSum
  , Norm
  , Fuse
  , FuseNorm
  , FuseTensor
  , Stabilize
  , Mult
  , Mults
  , NOf
  , FuseIdemMult
  , HomDim
  ) where

import Data.Kind (Constraint, Type)
import Experiments.Fusion.Theory (FiniteIrr (..), FusionTheory (..), LabelEq)
import GHC.TypeLits (Nat, type (*), type (+), type (-))

--------------------------------------------------------------------------------
-- Trees
--------------------------------------------------------------------------------

-- | Formal objects: simples, tensor, binary sums.
data Obj lab
  = Atom lab
  | Tensor (Obj lab) (Obj lab)
  | Sum (Obj lab) (Obj lab)

--------------------------------------------------------------------------------
-- Norm
--------------------------------------------------------------------------------

type family FlattenSum (a :: Obj lab) (b :: Obj lab) :: Obj lab where
  FlattenSum ('Sum a b) c = FlattenSum a (FlattenSum b c)
  FlattenSum a ('Sum b c) = 'Sum a (FlattenSum b c)
  FlattenSum a b = 'Sum a b

-- | Distribute @⊗@ over @⊕@, right-flatten sums. Does /not/ apply @FuseN@.
type family Norm (a :: Obj lab) :: Obj lab where
  Norm ('Atom s) = 'Atom s
  Norm ('Tensor ('Sum a b) c) = Norm ('Sum ('Tensor a c) ('Tensor b c))
  Norm ('Tensor a ('Sum b c)) = Norm ('Sum ('Tensor a b) ('Tensor a c))
  Norm ('Tensor a b) = 'Tensor (Norm a) (Norm b)
  Norm ('Sum ('Sum a b) c) = Norm ('Sum a ('Sum b c))
  Norm ('Sum a b) = FlattenSum (Norm a) (Norm b)

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
  ReplicateObj n a = 'Sum a (ReplicateObj (n - 1) a)

-- | Expand @FuseN@ entries to a right-nested sum of atoms (duplicates = multiplicity).
type family AtomsFromN (ns :: [(lab, Nat)]) :: Obj lab where
  AtomsFromN '[ '(s, n)] = ReplicateObj n ('Atom s)
  AtomsFromN ('(s, n) ': rest) =
    FlattenSum (ReplicateObj n ('Atom s)) (AtomsFromN rest)

--------------------------------------------------------------------------------
-- Fuse
--------------------------------------------------------------------------------

type family FuseLeft
  (t :: Type)
  (u :: lab)
  (b :: Obj lab)
  (isUnit :: Bool) :: Obj lab where
  FuseLeft _t _u b 'True = b
  FuseLeft t u ('Atom b) 'False = AtomsFromN (FuseN t u b)
  FuseLeft t u b 'False = FuseNorm t (Norm ('Tensor ('Atom u) b))

type family FuseRight
  (t :: Type)
  (a :: Obj lab)
  (u :: lab)
  (isUnit :: Bool) :: Obj lab where
  FuseRight _t a _u 'True = a
  FuseRight t ('Atom a) u 'False = AtomsFromN (FuseN t a u)
  FuseRight t a u 'False = FuseNorm t (Norm ('Tensor a ('Atom u)))

type family FuseTensorPair (t :: Type) (a :: Obj lab) (b :: Obj lab) :: Obj lab where
  FuseTensorPair t ('Atom u) b =
    FuseLeft t u b (LabelEq u (UnitLab t))
  FuseTensorPair t a ('Atom u) =
    FuseRight t a u (LabelEq u (UnitLab t))
  FuseTensorPair t a b = FuseNorm t (Norm ('Tensor a b))

-- | Fuse a tensor tree using @FuseN@ \/ unitors, then re-@Norm@.
type family FuseTensor (t :: Type) (a :: Obj lab) :: Obj lab where
  FuseTensor _t ('Atom s) = 'Atom s
  FuseTensor t ('Sum a b) = FlattenSum (FuseTensor t a) (FuseTensor t b)
  FuseTensor t ('Tensor a b) =
    FuseTensorPair t (FuseTensor t a) (FuseTensor t b)

type family FuseNorm (t :: Type) (a :: Obj lab) :: Obj lab where
  FuseNorm _t ('Atom s) = 'Atom s
  FuseNorm t ('Tensor a b) = FuseTensor t ('Tensor a b)
  FuseNorm t ('Sum a b) = FlattenSum (FuseNorm t a) (FuseNorm t b)

--------------------------------------------------------------------------------
-- Stabilize (Irr order)
--------------------------------------------------------------------------------

type family AppendObj (xs :: [Obj lab]) (ys :: [Obj lab]) :: [Obj lab] where
  AppendObj '[] ys = ys
  AppendObj (x ': xs) ys = x ': AppendObj xs ys

type family CollectSimples (t :: Type) (a :: Obj lab) :: [Obj lab] where
  CollectSimples _t ('Atom s) = '[ 'Atom s]
  CollectSimples t ('Sum a b) =
    AppendObj (CollectSimples t a) (CollectSimples t b)
  CollectSimples t ('Tensor a b) =
    CollectSimples t (FuseTensor t ('Tensor a b))

type family FilterLab (s :: lab) (xs :: [Obj lab]) :: [Obj lab] where
  FilterLab _s '[] = '[]
  FilterLab s ('Atom s ': xs) = 'Atom s ': FilterLab s xs
  FilterLab s ('Atom _t ': xs) = FilterLab s xs
  FilterLab s (_x ': xs) = FilterLab s xs

type family SortByIrr (irr :: [lab]) (xs :: [Obj lab]) :: [Obj lab] where
  SortByIrr '[] _xs = '[]
  SortByIrr (s ': ss) xs = AppendObj (FilterLab s xs) (SortByIrr ss xs)

type family SpineFrom (xs :: [Obj lab]) :: Obj lab where
  SpineFrom '[x] = x
  SpineFrom (x ': y ': ys) = 'Sum x (SpineFrom (y ': ys))

type family Stabilize (t :: Type) (a :: Obj lab) :: Obj lab where
  Stabilize t a = SpineFrom (SortByIrr (Irr t) (CollectSimples t a))

type family Fuse (t :: Type) (a :: Obj lab) :: Obj lab where
  Fuse t a = Stabilize t (FuseNorm t (Norm a))

--------------------------------------------------------------------------------
-- Multiplicities
--------------------------------------------------------------------------------

type family DeltaLab (s :: lab) (r :: lab) :: Nat where
  DeltaLab s s = 1
  DeltaLab _s _r = 0

-- | @n_s(X)@: multiplicity of simple @s@ in object @X@.
type family Mult (t :: Type) (s :: lab) (a :: Obj lab) :: Nat where
  Mult _t s ('Atom r) = DeltaLab s r
  Mult t s ('Sum a b) = Mult t s a + Mult t s b
  Mult t s ('Tensor a b) = MultTensor t s a b (Irr t)

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
