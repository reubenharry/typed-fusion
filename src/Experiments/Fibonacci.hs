{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Fibonacci fusion category (layered).
--
-- * __Trees__: @'One@, @'Tau@, @'Tensor@, @'Sum@ (general summands).
-- * __'Norm@__: distribute @⊗@ over @⊕@, right-associate sums → coalesced
--   sum of tensor trees.
-- * __'Fuse@__: @Stabilize ∘ FuseNorm ∘ Norm@ — fuse each tensor (@N@ on
--   @τ⊗τ@, unitors), flatten, then sort simples (@𝟙@ before @τ@) for a
--   stable sum spine (no multiplicities; duplicate @τ@ summands allowed).
-- * __Hom__: sector matrices @HomBlocks@ on fused multiplicities
--   @MultOne@ \/ @MultTau@ (see @Fibonacci.md@ §4, §12).
-- * __Compose__: one generic @composeBlocks@ (per-sector matrix multiply);
--   @cup@ carries @φ@ so the snake is ordinary composition.
module Experiments.Fibonacci
  ( -- * Labels \/ objects
    Simple (..)
  , FibObj (..)
  , Norm
  , Fuse
  , FuseNorm
  , Stabilize
  , MultOne
  , MultTau
  , HomDim
  , TauTau
  , OnePlusTau
  , AssocL
  , AssocR
    -- * Hom
  , HomBlocks (..)
  , Fib (..)
  , SFib (..)
  , KnownFib (..)
  , composeBlocks
  , idBlocks
  , zeroBlocks
  , phi
  , cup
  , cap
  , composeFib
  , zeroMor
    -- * Fuse \/ split
  , fuse
  , split
    -- * F \/ R (typed stubs)
  , fmove
  , rmove
    -- * Fusion theory
  , FibTh
  ) where

import Control.Category.Constrained.Prelude (Category (..))
import Data.Complex (Complex (..))
import Data.Proxy (Proxy (..))
import Experiments.Categorical.Bifunctor (Bifunctor (..), PFunctor (..), QFunctor (..))
import Experiments.Fusion.Theory (FusionTheory (..))
import GHC.TypeLits (KnownNat, Nat, natVal, type (*), type (+))
import qualified Numeric.LinearAlgebra as LA
import Numeric.LinearAlgebra.Static
  ( Domain (mul)
  , M
  , Sized (fromList, unwrap)
  , konst
  )
import Prelude hiding (id, (.))

--------------------------------------------------------------------------------
-- Fusion theory (N-symbols on simple labels)
--------------------------------------------------------------------------------

data FibTh

data Simple
  = SOne
  | STau

instance FusionTheory Simple FibTh where
  type UnitLab FibTh = 'SOne
  type FuseN FibTh 'SOne 'SOne = '[ '( 'SOne, 1)]
  type FuseN FibTh 'SOne 'STau = '[ '( 'STau, 1)]
  type FuseN FibTh 'STau 'SOne = '[ '( 'STau, 1)]
  type FuseN FibTh 'STau 'STau = '[ '( 'SOne, 1), '( 'STau, 1)]

--------------------------------------------------------------------------------
-- Objects
--------------------------------------------------------------------------------

-- | Trees: simples, tensor, and binary sums of /arbitrary/ objects.
data FibObj
  = One
  | Tau
  | Tensor FibObj FibObj
  | Sum FibObj FibObj

type TauTau = 'Tensor 'Tau 'Tau
type OnePlusTau = 'Sum 'One 'Tau
type AssocL = 'Tensor TauTau 'Tau
type AssocR = 'Tensor 'Tau TauTau

--------------------------------------------------------------------------------
-- Norm: coalesced sum of tensor trees
--------------------------------------------------------------------------------

-- | Right-associate and concatenate sum spines.
type family FlattenSum (a :: FibObj) (b :: FibObj) :: FibObj where
  FlattenSum ('Sum a b) c = FlattenSum a (FlattenSum b c)
  FlattenSum a ('Sum b c) = 'Sum a (FlattenSum b c)
  FlattenSum a b = 'Sum a b

-- | Distribute @⊗@ over @⊕@, normalize summands, right-flatten sums.
--
-- Result shape: a (possibly trivial) right-nested @'Sum@ of tensor trees
-- (and simples). Does /not/ fuse @τ⊗τ@.
type family Norm (a :: FibObj) :: FibObj where
  Norm 'One = 'One
  Norm 'Tau = 'Tau
  Norm ('Tensor ('Sum a b) c) = Norm ('Sum ('Tensor a c) ('Tensor b c))
  Norm ('Tensor a ('Sum b c)) = Norm ('Sum ('Tensor a b) ('Tensor a c))
  Norm ('Tensor a b) = 'Tensor (Norm a) (Norm b)
  Norm ('Sum ('Sum a b) c) = Norm ('Sum a ('Sum b c))
  Norm ('Sum a b) = FlattenSum (Norm a) (Norm b)

--------------------------------------------------------------------------------
-- Fuse: fuse each tensor, flatten sum-of-sums
--------------------------------------------------------------------------------

-- | Fuse a tensor tree: unitors, @τ⊗τ ↦ 𝟙⊕τ@, then re-@'Norm@ and recurse so
-- nested tensors distribute and fuse to a sum of simples.
type family FuseTensor (t :: FibObj) :: FibObj where
  FuseTensor 'One = 'One
  FuseTensor 'Tau = 'Tau
  FuseTensor ('Tensor 'One a) = FuseTensor a
  FuseTensor ('Tensor a 'One) = FuseTensor a
  FuseTensor ('Tensor 'Tau 'Tau) = 'Sum 'One 'Tau
  FuseTensor ('Tensor a b) =
    FuseNorm (Norm ('Tensor (FuseTensor a) (FuseTensor b)))
  FuseTensor ('Sum a b) = FlattenSum (FuseTensor a) (FuseTensor b)

-- | Fuse a /normalized/ object: map each summand, flatten.
type family FuseNorm (a :: FibObj) :: FibObj where
  FuseNorm 'One = 'One
  FuseNorm 'Tau = 'Tau
  FuseNorm ('Tensor a b) = FuseTensor ('Tensor a b)
  FuseNorm ('Sum a b) = FlattenSum (FuseNorm a) (FuseNorm b)

--------------------------------------------------------------------------------
-- Stabilize: canonical order of simple summands (𝟙 then τ)
--------------------------------------------------------------------------------

type family AppendFib (xs :: [FibObj]) (ys :: [FibObj]) :: [FibObj] where
  AppendFib '[] ys = ys
  AppendFib (x ': xs) ys = x ': AppendFib xs ys

-- | Flatten a fused sum to a list of simple atoms.
type family CollectSimples (a :: FibObj) :: [FibObj] where
  CollectSimples 'One = '[ 'One]
  CollectSimples 'Tau = '[ 'Tau]
  CollectSimples ('Sum a b) =
    AppendFib (CollectSimples a) (CollectSimples b)
  -- Residual tensor: fuse further (should be rare after 'FuseNorm').
  CollectSimples ('Tensor a b) =
    CollectSimples (FuseTensor ('Tensor a b))

type family FilterOne (xs :: [FibObj]) :: [FibObj] where
  FilterOne '[] = '[]
  FilterOne ('One ': xs) = 'One ': FilterOne xs
  FilterOne ('Tau ': xs) = FilterOne xs

type family FilterTau (xs :: [FibObj]) :: [FibObj] where
  FilterTau '[] = '[]
  FilterTau ('Tau ': xs) = 'Tau ': FilterTau xs
  FilterTau ('One ': xs) = FilterTau xs

-- | Stable order: all @𝟙@ summands, then all @τ@ (duplicates kept).
type family SortSimples (xs :: [FibObj]) :: [FibObj] where
  SortSimples xs = AppendFib (FilterOne xs) (FilterTau xs)

-- | Right-nested @'Sum@ spine from a non-empty atom list.
type family SpineFrom (xs :: [FibObj]) :: FibObj where
  SpineFrom '[x] = x
  SpineFrom (x ': y ': ys) = 'Sum x (SpineFrom (y ': ys))

-- | Canonical fused form for comparison: sorted simple summands.
type family Stabilize (a :: FibObj) :: FibObj where
  Stabilize a = SpineFrom (SortSimples (CollectSimples a))

-- | Full fuse: normalize, fuse tensors, flatten, stabilize.
type family Fuse (a :: FibObj) :: FibObj where
  Fuse a = Stabilize (FuseNorm (Norm a))

--------------------------------------------------------------------------------
-- Fused multiplicities
--------------------------------------------------------------------------------

type family CountOne (xs :: [FibObj]) :: Nat where
  CountOne '[] = 0
  CountOne ('One ': xs) = 1 + CountOne xs
  CountOne ('Tau ': xs) = CountOne xs

type family CountTau (xs :: [FibObj]) :: Nat where
  CountTau '[] = 0
  CountTau ('Tau ': xs) = 1 + CountTau xs
  CountTau ('One ': xs) = CountTau xs

-- | Multiplicity of @𝟙@ in @Fuse a@.
type family MultOne (a :: FibObj) :: Nat where
  MultOne a = CountOne (CollectSimples (Fuse a))

-- | Multiplicity of @τ@ in @Fuse a@.
type family MultTau (a :: FibObj) :: Nat where
  MultTau a = CountTau (CollectSimples (Fuse a))

-- | Total Hom dimension (derived): @n₁(X) n₁(Y) + nτ(X) nτ(Y)@.
type family HomDim (a :: FibObj) (b :: FibObj) :: Nat where
  HomDim a b = MultOne a * MultOne b + MultTau a * MultTau b

--------------------------------------------------------------------------------
-- Singletons / objects of the category
--------------------------------------------------------------------------------

data SFib (a :: FibObj) where
  SFOne :: SFib 'One
  SFTau :: SFib 'Tau
  SFTauTau :: SFib TauTau
  SFOnePlusTau :: SFib OnePlusTau

class KnownFib (a :: FibObj) where
  fibSing :: SFib a

instance KnownFib 'One where fibSing = SFOne
instance KnownFib 'Tau where fibSing = SFTau
instance KnownFib TauTau where fibSing = SFTauTau
instance KnownFib OnePlusTau where fibSing = SFOnePlusTau

--------------------------------------------------------------------------------
-- Sector Hom blocks and composition
--------------------------------------------------------------------------------

-- | Skeletal Hom: one matrix per simple label.
--
-- @blkOne :: M n1y n1x@ is the @𝟙@-sector map
-- (@n1x = MultOne@ domain, @n1y = MultOne@ codomain); likewise @blkTau@.
data HomBlocks (n1x :: Nat) (ntx :: Nat) (n1y :: Nat) (nty :: Nat) = HomBlocks
  { blkOne :: M n1y n1x
  , blkTau :: M nty ntx
  }

eyeM :: forall n. KnownNat n => M n n
eyeM =
  let n = fromIntegral (natVal (Proxy @n)) :: Int
   in fromList
        [ if i == j then 1 else 0
        | i <- [0 .. n - 1]
        , j <- [0 .. n - 1]
        ]

idBlocks
  :: forall n1 nt
   . (KnownNat n1, KnownNat nt)
  => HomBlocks n1 nt n1 nt
idBlocks = HomBlocks (eyeM @n1) (eyeM @nt)

zeroBlocks
  :: forall n1x ntx n1y nty
   . (KnownNat n1x, KnownNat ntx, KnownNat n1y, KnownNat nty)
  => HomBlocks n1x ntx n1y nty
zeroBlocks = HomBlocks (konst 0) (konst 0)

-- | Per-sector matrix multiply: @(g ∘ f)_s = G_s F_s@.
composeBlocks
  :: forall n1x ntx n1y nty n1z ntz
   . ( KnownNat n1x
     , KnownNat ntx
     , KnownNat n1y
     , KnownNat nty
     , KnownNat n1z
     , KnownNat ntz
     )
  => HomBlocks n1y nty n1z ntz
  -> HomBlocks n1x ntx n1y nty
  -> HomBlocks n1x ntx n1z ntz
composeBlocks (HomBlocks g1 gt) (HomBlocks f1 ft) =
  HomBlocks (mul g1 f1) (mul gt ft)

--------------------------------------------------------------------------------
-- Morphisms
--------------------------------------------------------------------------------

newtype Fib (a :: FibObj) (b :: FibObj) = Fib
  { unFib :: HomBlocks (MultOne a) (MultTau a) (MultOne b) (MultTau b) }

phi :: Complex Double
phi = ((1 + sqrt 5) / 2) :+ 0

-- | Coevaluation @𝟙 → τ⊗τ@. Coefficient @φ@ in the @𝟙@-channel so
-- @cap ∘ cup = φ · id@ under @composeBlocks@.
cup :: Fib 'One TauTau
cup =
  Fib $
    HomBlocks
      (fromList [phi] :: M 1 1)
      (konst 0 :: M 1 0)

cap :: Fib TauTau 'One
cap =
  Fib $
    HomBlocks
      (fromList [1] :: M 1 1)
      (konst 0 :: M 0 1)

-- | Fusion iso as id on the common fused skeleton @(n₁,nτ)=(1,1)@.
fuse :: Fib TauTau OnePlusTau
fuse = Fib idBlocks

split :: Fib OnePlusTau TauTau
split = Fib idBlocks

fmove :: Fib AssocL AssocR
fmove = undefined

rmove :: Fib TauTau TauTau
rmove = undefined

-- | Zero morphism (both sectors).
zeroMor
  :: forall a c
   . ( KnownNat (MultOne a)
     , KnownNat (MultTau a)
     , KnownNat (MultOne c)
     , KnownNat (MultTau c)
     )
  => Fib a c
zeroMor = Fib zeroBlocks

composeFib
  :: forall a b c
   . ( KnownNat (MultOne a)
     , KnownNat (MultTau a)
     , KnownNat (MultOne b)
     , KnownNat (MultTau b)
     , KnownNat (MultOne c)
     , KnownNat (MultTau c)
     )
  => Fib b c
  -> Fib a b
  -> Fib a c
composeFib (Fib g) (Fib f) = Fib (composeBlocks g f)

--------------------------------------------------------------------------------
-- Category
--------------------------------------------------------------------------------

-- | Multiplicities known so @id@ \/ @composeBlocks@ need no object-name table.
type FibObject a =
  ( KnownFib a
  , KnownNat (MultOne a)
  , KnownNat (MultTau a)
  )

instance Category Fib where
  type Object Fib a = FibObject a

  id :: forall a. Object Fib a => Fib a a
  id = Fib idBlocks

  (.)
    :: forall a b c
     . (Object Fib a, Object Fib b, Object Fib c)
    => Fib b c
    -> Fib a b
    -> Fib a c
  (.) = composeFib @a @b @c

--------------------------------------------------------------------------------
-- Tensor biendofunctor (tree layer)
--------------------------------------------------------------------------------

-- | End(τ) scalar (τ-sector @1×1@).
scalarEndTau :: Fib 'Tau 'Tau -> Complex Double
scalarEndTau (Fib (HomBlocks _ t)) =
  LA.atIndex (unwrap t) (0, 0)

-- | Scale both fused channels of @End(τ⊗τ)@ by a scalar.
scaleEndTauTau :: Complex Double -> Fib TauTau TauTau
scaleEndTauTau s =
  Fib $
    HomBlocks
      (fromList [s] :: M 1 1)
      (fromList [s] :: M 1 1)

instance PFunctor Tensor Fib Fib where
  first
    :: forall a b c
     . (Object Fib a, Object Fib b, Object Fib (Tensor a c), Object Fib (Tensor b c))
    => Fib a b
    -> Fib (Tensor a c) (Tensor b c)
  first f =
    case (fibSing @a, fibSing @b, fibSing @(Tensor a c), fibSing @(Tensor b c)) of
      (SFTau, SFTau, SFTauTau, SFTauTau) ->
        scaleEndTauTau (scalarEndTau f)
      _ ->
        error "Fib Tensor first: only End(τ) → End(τ⊗τ) under current KnownFib"

instance QFunctor Tensor Fib Fib where
  second
    :: forall a b c
     . (Object Fib a, Object Fib b, Object Fib (Tensor c a), Object Fib (Tensor c b))
    => Fib a b
    -> Fib (Tensor c a) (Tensor c b)
  second g =
    case (fibSing @a, fibSing @b, fibSing @(Tensor c a), fibSing @(Tensor c b)) of
      (SFTau, SFTau, SFTauTau, SFTauTau) ->
        scaleEndTauTau (scalarEndTau g)
      _ ->
        error "Fib Tensor second: only End(τ) → End(τ⊗τ) under current KnownFib"

instance Bifunctor Tensor Fib Fib Fib where
  bimap
    :: forall a b c d
     . ( Object Fib a
       , Object Fib b
       , Object Fib c
       , Object Fib d
       , Object Fib (Tensor a c)
       , Object Fib (Tensor b d)
       )
    => Fib a b
    -> Fib c d
    -> Fib (Tensor a c) (Tensor b d)
  bimap f g =
    case
      ( fibSing @a
      , fibSing @b
      , fibSing @c
      , fibSing @d
      , fibSing @(Tensor a c)
      , fibSing @(Tensor b d)
      ) of
      (SFTau, SFTau, SFTau, SFTau, SFTauTau, SFTauTau) ->
        scaleEndTauTau (scalarEndTau f * scalarEndTau g)
      _ ->
        error "Fib Tensor bimap: only End(τ)×End(τ)→End(τ⊗τ) under current KnownFib"
