{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
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
-- * __Hom__: sector matrices @HomBlocks@ on multiplicities @MultOne@ \/
--   @MultTau@ (@N@-bilinear on @'Tensor@, additive on @'Sum@).
-- * __Compose__: @composeBlocks@ (per-sector matrix multiply); @cup@ carries @φ@.
-- * __Fuse functor__: @fuseMap@ reindexes object parameters (id on blocks).
-- * __Tensor bifunctor__: @tensorBlocks@ \/ @bimap@ — Kronecker via @N@-symbols.
-- * __Monoidal \/ braided__: @Associative@\/@Monoidal@\/@Braided@ on @Tensor@
--   (@associateBlocks@\/@braidBlocks@\/unitors; not 'Symmetric').
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
  , FuseIdemMult
  , TauTau
  , OnePlusTau
    -- * KnownNat bundles
  , KnownMult
  , KnownNTensor
  , KnownAssoc
  , KnownTensorMult
  , KnownAssocMult
    -- * Hom
  , HomBlocks (..)
  , Fib (..)
  , composeBlocks
  , idBlocks
  , zeroBlocks
  , tensorBlocks
  , braidBlocks
  , associateBlocks
  , disassociateBlocks
  , phi
  , phiInv
  , phiInvSqrt
  , cup
  , cap
  , zeroMor
  , fuseMap
  , eqFib
    -- * Fuse \/ split
  , fuse
  , split
    -- * Fusion theory
  , FibTh
  ) where

import Control.Category.Constrained.Prelude (Category (..))
import Control.Monad (guard)
import Data.Complex (Complex (..))
import Data.Kind (Constraint)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import Experiments.Categorical.Associative (Associative (..))
import Experiments.Categorical.Bifunctor (Bifunctor (..), PFunctor (..), QFunctor (..))
import Experiments.Categorical.Braided (Braided (..))
import Experiments.Categorical.Monoidal (Monoidal (..))
import Experiments.Fusion.Theory (FusionTheory (..))
import GHC.TypeLits (KnownNat, Nat, natVal, type (*), type (+))
import qualified Numeric.LinearAlgebra as LA
import Numeric.LinearAlgebra.Static
  ( Domain (mul)
  , M
  , Sized (create, fromList, unwrap)
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
-- Multiplicities (N-bilinear / ⊕-additive — monoidal on the nose)
--------------------------------------------------------------------------------

-- | Multiplicity of @𝟙@. For @'Tensor@, uses Fib @N@-symbols:
-- @n₁(a⊗b) = n₁(a)n₁(b) + nτ(a)nτ(b)@.
type family MultOne (a :: FibObj) :: Nat where
  MultOne 'One = 1
  MultOne 'Tau = 0
  MultOne ('Sum a b) = MultOne a + MultOne b
  MultOne ('Tensor a b) =
    MultOne a * MultOne b + MultTau a * MultTau b

-- | Multiplicity of @τ@:
-- @nτ(a⊗b) = n₁(a)nτ(b) + nτ(a)n₁(b) + nτ(a)nτ(b)@.
type family MultTau (a :: FibObj) :: Nat where
  MultTau 'One = 0
  MultTau 'Tau = 1
  MultTau ('Sum a b) = MultTau a + MultTau b
  MultTau ('Tensor a b) =
    MultOne a * MultTau b + MultTau a * MultOne b + MultTau a * MultTau b

-- | Total Hom dimension (derived): @n₁(X) n₁(Y) + nτ(X) nτ(Y)@.
type family HomDim (a :: FibObj) (b :: FibObj) :: Nat where
  HomDim a b = MultOne a * MultOne b + MultTau a * MultTau b

-- | @Fuse@ does not change multiplicities (@Fuse@ idempotent on @N@-counts).
type FuseIdemMult (a :: FibObj) =
  ( MultOne a ~ MultOne (Fuse a)
  , MultTau a ~ MultTau (Fuse a)
  )

--------------------------------------------------------------------------------
-- KnownNat bundles (generated from N-bilinear Mult formulas)
--------------------------------------------------------------------------------

-- | Both sector multiplicities of an object are 'KnownNat'.
type KnownMult (a :: FibObj) =
  ( KnownNat (MultOne a)
  , KnownNat (MultTau a)
  )

-- | Fold 'KnownNat' over a type-level list.
type family AllKnownNat (ns :: [Nat]) :: Constraint where
  AllKnownNat '[] = ()
  AllKnownNat (n ': ns) = (KnownNat n, AllKnownNat ns)

type family AppendNat (xs :: [Nat]) (ys :: [Nat]) :: [Nat] where
  AppendNat '[] ys = ys
  AppendNat (x ': xs) ys = x ': AppendNat xs ys

-- | @n₁@ / @nτ@ of an N-bilinear tensor of two multiplicity pairs
-- (matches 'MultOne' \/ 'MultTau' on @'Tensor@). Inline in 'NTensorNats'
-- (do not wrap in a type family — 'KnownNat' solvers need the @*@\/@+@ spine).
type N1Pair n1a nta n1b ntb = n1a * n1b + nta * ntb
type NTPair n1a nta n1b ntb = (n1a * ntb + nta * n1b) + nta * ntb

-- | Nat expressions needed for @Hom@ Kronecker \/ braid of two pairs
-- (includes both factor orders for braiding).
type family NTensorNats (n1a :: Nat) (nta :: Nat) (n1b :: Nat) (ntb :: Nat) :: [Nat] where
  NTensorNats n1a nta n1b ntb =
    '[ n1a * n1b
     , n1b * n1a
     , nta * ntb
     , ntb * nta
     , n1a * ntb
     , ntb * n1a
     , nta * n1b
     , n1b * nta
     , n1a * n1b + nta * ntb
     , n1b * n1a + ntb * nta
     , n1a * ntb + nta * n1b
     , n1b * nta + ntb * n1a
     , (n1a * ntb + nta * n1b) + nta * ntb
     , (n1b * nta + ntb * n1a) + ntb * nta
     ]

-- | 'KnownNat' for two multiplicity pairs and their N-tensor intermediates.
type KnownNTensor (n1a :: Nat) (nta :: Nat) (n1b :: Nat) (ntb :: Nat) =
  ( KnownNat n1a
  , KnownNat nta
  , KnownNat n1b
  , KnownNat ntb
  , AllKnownNat (NTensorNats n1a nta n1b ntb)
  )

-- | Nat expressions for the associator @((a⊗b)⊗c)@ \/ @(a⊗(b⊗c))@.
type family AssocNats
  (n1a :: Nat) (nta :: Nat)
  (n1b :: Nat) (ntb :: Nat)
  (n1c :: Nat) (ntc :: Nat) :: [Nat] where
  AssocNats n1a nta n1b ntb n1c ntc =
    AppendNat
      (NTensorNats n1a nta n1b ntb)
      ( AppendNat
          (NTensorNats n1b ntb n1c ntc)
          ( AppendNat
              ( NTensorNats
                  (n1a * n1b + nta * ntb)
                  ((n1a * ntb + nta * n1b) + nta * ntb)
                  n1c
                  ntc
              )
              ( NTensorNats
                  n1a
                  nta
                  (n1b * n1c + ntb * ntc)
                  ((n1b * ntc + ntb * n1c) + ntb * ntc)
              )
          )
      )

type KnownAssoc
  (n1a :: Nat) (nta :: Nat)
  (n1b :: Nat) (ntb :: Nat)
  (n1c :: Nat) (ntc :: Nat) =
  ( KnownNat n1a
  , KnownNat nta
  , KnownNat n1b
  , KnownNat ntb
  , KnownNat n1c
  , KnownNat ntc
  , AllKnownNat (AssocNats n1a nta n1b ntb n1c ntc)
  )

-- | Object-level: N-tensor of @Mult* a@ with @Mult* b@.
type KnownTensorMult (a :: FibObj) (b :: FibObj) =
  KnownNTensor (MultOne a) (MultTau a) (MultOne b) (MultTau b)

-- | Object-level associator on @a,b,c@.
type KnownAssocMult (a :: FibObj) (b :: FibObj) (c :: FibObj) =
  KnownAssoc
    (MultOne a) (MultTau a)
    (MultOne b) (MultTau b)
    (MultOne c) (MultTau c)

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
-- Skeletal tensor product of Hom blocks (N-symbol / Kronecker)
--------------------------------------------------------------------------------

toLA :: (KnownNat m, KnownNat n) => M m n -> LA.Matrix (Complex Double)
toLA = unwrap

fromLA
  :: forall m n
   . (KnownNat m, KnownNat n)
  => LA.Matrix (Complex Double)
  -> M m n
fromLA m =
  fromMaybe (error "Fibonacci.fromLA: dimension mismatch") (create m)

natI :: forall n. KnownNat n => Int
natI = fromIntegral (natVal (Proxy @n))

-- | Kronecker product of static matrices.
kronM
  :: forall m n p q
   . ( KnownNat m
     , KnownNat n
     , KnownNat p
     , KnownNat q
     , KnownNat (m * p)
     , KnownNat (n * q)
     )
  => M m n
  -> M p q
  -> M (m * p) (n * q)
kronM a b = fromLA (LA.kronecker (toLA a) (toLA b))

-- | Block diagonal @[A 0; 0 B]@.
blockDiag2
  :: forall a b c d
   . ( KnownNat a
     , KnownNat b
     , KnownNat c
     , KnownNat d
     , KnownNat (a + c)
     , KnownNat (b + d)
     )
  => M a b
  -> M c d
  -> M (a + c) (b + d)
blockDiag2 u v =
  fromLA $
    LA.fromBlocks
      [ [toLA u, LA.konst 0 (natI @a, natI @d)]
      , [LA.konst 0 (natI @c, natI @b), toLA v]
      ]

-- | Block diagonal of three blocks.
blockDiag3
  :: forall a b c d e f
   . ( KnownNat a
     , KnownNat b
     , KnownNat c
     , KnownNat d
     , KnownNat e
     , KnownNat f
     , KnownNat (a + c)
     , KnownNat (b + d)
     , KnownNat ((a + c) + e)
     , KnownNat ((b + d) + f)
     )
  => M a b
  -> M c d
  -> M e f
  -> M ((a + c) + e) ((b + d) + f)
blockDiag3 u v w = blockDiag2 (blockDiag2 u v) w

-- | Tensor product of skeletal Homs via Fib @N@-symbols.
--
-- Basis order (matches @Norm@ distribute then Ones-before-Taus):
--
-- * 𝟙-sector cols\/rows: @(𝟙⊗𝟙)@ pairs, then @(τ⊗τ → 𝟙)@ pairs;
-- * τ-sector: @(𝟙⊗τ)@, then @(τ⊗𝟙)@, then @(τ⊗τ → τ)@.
--
-- Block form: @R₁ = diag(F₁⊗G₁, Fτ⊗Gτ)@,
-- @Rτ = diag(F₁⊗Gτ, Fτ⊗G₁, Fτ⊗Gτ)@.
tensorBlocks
  :: forall n1x ntx n1y nty n1z ntz n1w ntw
   . ( KnownNTensor n1x ntx n1z ntz
     , KnownNTensor n1y nty n1w ntw
     )
  => HomBlocks n1x ntx n1y nty
  -> HomBlocks n1z ntz n1w ntw
  -> HomBlocks
      (n1x * n1z + ntx * ntz)
      ((n1x * ntz + ntx * n1z) + ntx * ntz)
      (n1y * n1w + nty * ntw)
      ((n1y * ntw + nty * n1w) + nty * ntw)
tensorBlocks (HomBlocks f1 ft) (HomBlocks g1 gt) =
  HomBlocks
    (blockDiag2 (kronM f1 g1) (kronM ft gt))
    (blockDiag3 (kronM f1 gt) (kronM ft g1) (kronM ft gt))

--------------------------------------------------------------------------------
-- Skeletal braiding (R-symbols extended by N-bilinearity)
--------------------------------------------------------------------------------

-- | Simple-label R-matrix phases (Bonderson Fibonacci).
-- @R^{𝟙𝟙}=R^{𝟙τ}=R^{τ𝟙}=1@; nontrivial @R^{ττ}@ below.
rPhaseTauTauOne :: Complex Double
rPhaseTauTauOne =
  let i = 0 :+ 1
   in exp (-4 * pi * i / 5)

rPhaseTauTauTau :: Complex Double
rPhaseTauTauTau =
  let i = 0 :+ 1
   in exp (3 * pi * i / 5)

-- | Commutation matrix for @n×m@ Kronecker factors: @(i,j) ↦ φ · (j,i)@.
-- Size @(m*n) × (n*m)@.
commuteKron
  :: Int
  -> Int
  -> Complex Double
  -> LA.Matrix (Complex Double)
commuteKron n m phase
  | n == 0 || m == 0 = LA.konst 0 (m * n, n * m)
  | otherwise =
      LA.accum (LA.konst 0 (m * n, n * m)) const $
        [ ((j * n + i, i * m + j), phase)
        | i <- [0 .. n - 1]
        , j <- [0 .. m - 1]
        ]

-- | Braiding @X⊗Y → Y⊗X@ on skeletal Hom, same basis order as 'tensorBlocks'.
--
-- * 𝟙-sector: swap @(𝟙⊗𝟙)@ pairs (phase @R^{𝟙𝟙}=1@) and @(τ⊗τ→𝟙)@ pairs
--   (phase @R^{ττ}_𝟙@);
-- * τ-sector: @(𝟙⊗τ) → (τ⊗𝟙)@ and @(τ⊗𝟙) → (𝟙⊗τ)@ (phases @1@), and
--   @(τ⊗τ→τ)@ with @R^{ττ}_τ@.
braidBlocks
  :: forall n1a nta n1b ntb
   . KnownNTensor n1a nta n1b ntb
  => HomBlocks
      (n1a * n1b + nta * ntb)
      ((n1a * ntb + nta * n1b) + nta * ntb)
      (n1b * n1a + ntb * nta)
      ((n1b * nta + ntb * n1a) + ntb * nta)
braidBlocks =
  let n1a = natI @n1a
      nta = natI @nta
      n1b = natI @n1b
      ntb = natI @ntb
      onesDom = n1a * n1b
      onesCod = n1b * n1a
      tausDomOT = n1a * ntb
      tausDomTO = nta * n1b
      tausDomTT = nta * ntb
      tausCodOT = n1b * nta
      tausCodTO = ntb * n1a
      tausCodTT = ntb * nta
      oneBlk =
        LA.fromBlocks
          [ [commuteKron n1a n1b 1, LA.konst 0 (onesCod, nta * ntb)]
          , [LA.konst 0 (ntb * nta, onesDom), commuteKron nta ntb rPhaseTauTauOne]
          ]
      -- τ-sector rows = OT'|TO'|TT' (b⊗a), cols = OT|TO|TT (a⊗b):
      --   OT → TO' (R^{𝟙τ}), TO → OT' (R^{τ𝟙}), TT → TT' (R^{ττ}_τ).
      otToTo = commuteKron n1a ntb 1
      toToOt = commuteKron nta n1b 1
      ttToTt = commuteKron nta ntb rPhaseTauTauTau
      tauBlk =
        LA.fromBlocks
          [ [ LA.konst 0 (tausCodOT, tausDomOT)
            , toToOt
            , LA.konst 0 (tausCodOT, tausDomTT)
            ]
          , [ otToTo
            , LA.konst 0 (tausCodTO, tausDomTO)
            , LA.konst 0 (tausCodTO, tausDomTT)
            ]
          , [ LA.konst 0 (tausCodTT, tausDomOT)
            , LA.konst 0 (tausCodTT, tausDomTO)
            , ttToTt
            ]
          ]
   in HomBlocks (fromLA oneBlk) (fromLA tauBlk)

--------------------------------------------------------------------------------
-- Morphisms
--------------------------------------------------------------------------------

newtype Fib (a :: FibObj) (b :: FibObj) = Fib
  { unFib :: HomBlocks (MultOne a) (MultTau a) (MultOne b) (MultTau b) }

phi :: Complex Double
phi = ((1 + sqrt 5) / 2) :+ 0

-- | @φ⁻¹ = φ − 1@.
phiInv :: Complex Double
phiInv = 1 / phi

-- | @φ⁻¹ᐟ²@.
phiInvSqrt :: Complex Double
phiInvSqrt = sqrt phiInv

--------------------------------------------------------------------------------
-- Skeletal associator (F-symbols on the N-bilinear basis)
--------------------------------------------------------------------------------

-- | Simple fusion charges.
data Ch = C1 | Ct
  deriving (Eq)

canFuse :: Ch -> Ch -> Ch -> Bool
canFuse C1 C1 C1 = True
canFuse C1 Ct Ct = True
canFuse Ct C1 Ct = True
canFuse Ct Ct C1 = True
canFuse Ct Ct Ct = True
canFuse _ _ _ = False

-- | @F^{abc}_{d;e→f}@ amplitudes (@inv=False@) or @F^{-1}@ (@inv=True@).
-- Nontrivial only for @τττ@; otherwise the unique allowed @(e,f)@ has amp @1@.
fRow :: Bool -> Ch -> Ch -> Ch -> Ch -> Ch -> [(Ch, Complex Double)]
fRow inv Ct Ct Ct C1 Ct = [(Ct, if inv then phi else phiInv)]
fRow _ Ct Ct Ct Ct C1 =
  [(C1, phiInv), (Ct, phiInvSqrt)]
fRow _ Ct Ct Ct Ct Ct =
  [(C1, phiInvSqrt), (Ct, -phiInv)]
fRow _ a b c d e =
  [ (f, 1)
  | f <- [C1, Ct]
  , canFuse a b e
  , canFuse e c d
  , canFuse b c f
  , canFuse a f d
  ]

copiesOf :: Ch -> Int -> Int -> [Int]
copiesOf C1 n1 _ = [0 .. n1 - 1]
copiesOf Ct _ nt = [0 .. nt - 1]

-- | Ones-channel index of @x⊗y → 𝟙@.
idxOnesXY :: Int -> Int -> Int -> Int -> Ch -> Int -> Ch -> Int -> Maybe Int
idxOnesXY n1x _ntx n1y _nty C1 ix C1 iy
  | ix < n1x && iy < n1y = Just (ix * n1y + iy)
  | otherwise = Nothing
idxOnesXY n1x ntx n1y nty Ct tx Ct ty
  | tx < ntx && ty < nty = Just (n1x * n1y + tx * nty + ty)
  | otherwise = Nothing
idxOnesXY _ _ _ _ _ _ _ _ = Nothing

-- | Taus-channel index of @x⊗y → τ@.
idxTausXY :: Int -> Int -> Int -> Int -> Ch -> Int -> Ch -> Int -> Maybe Int
idxTausXY n1x _ntx _n1y nty C1 ix Ct ty
  | ix < n1x && ty < nty = Just (ix * nty + ty)
  | otherwise = Nothing
idxTausXY n1x ntx n1y nty Ct tx C1 iy
  | tx < ntx && iy < n1y = Just (n1x * nty + tx * n1y + iy)
  | otherwise = Nothing
idxTausXY n1x ntx n1y nty Ct tx Ct ty
  | tx < ntx && ty < nty = Just (n1x * nty + ntx * n1y + tx * nty + ty)
  | otherwise = Nothing
idxTausXY _ _ _ _ _ _ _ _ = Nothing

-- | Column in @((a⊗b)⊗c)@ ones sector for leaves + left intermediate @e@.
leftColOnes
  :: Int -> Int -> Int -> Int -> Int -> Int
  -> Ch -> Int -> Ch -> Int -> Ch -> Int -> Ch
  -> Maybe Int
leftColOnes n1a nta n1b ntb n1c ntc aCh aI bCh bI cCh cI eCh =
  let n1ab = n1a * n1b + nta * ntb
   in case eCh of
        C1 -> do
          guard (cCh == C1)
          eIdx <- idxOnesXY n1a nta n1b ntb aCh aI bCh bI
          Just (eIdx * n1c + cI)
        Ct -> do
          guard (cCh == Ct)
          eIdx <- idxTausXY n1a nta n1b ntb aCh aI bCh bI
          Just (n1ab * n1c + eIdx * ntc + cI)

-- | Row in @a⊗(b⊗c)@ ones sector for leaves + right intermediate @f@.
rightRowOnes
  :: Int -> Int -> Int -> Int -> Int -> Int
  -> Ch -> Int -> Ch -> Int -> Ch -> Int -> Ch
  -> Maybe Int
rightRowOnes n1a _nta n1b ntb n1c ntc aCh aI bCh bI cCh cI fCh =
  let n1bc = n1b * n1c + ntb * ntc
      ntbc = n1b * ntc + ntb * n1c + ntb * ntc
   in case aCh of
        C1 -> do
          guard (fCh == C1)
          fIdx <- idxOnesXY n1b ntb n1c ntc bCh bI cCh cI
          Just (aI * n1bc + fIdx)
        Ct -> do
          guard (fCh == Ct)
          fIdx <- idxTausXY n1b ntb n1c ntc bCh bI cCh cI
          Just (n1a * n1bc + aI * ntbc + fIdx)

-- | Column in @((a⊗b)⊗c)@ tau sector.
leftColTaus
  :: Int -> Int -> Int -> Int -> Int -> Int
  -> Ch -> Int -> Ch -> Int -> Ch -> Int -> Ch
  -> Maybe Int
leftColTaus n1a nta n1b ntb n1c ntc aCh aI bCh bI cCh cI eCh =
  let n1ab = n1a * n1b + nta * ntb
      ntab = n1a * ntb + nta * n1b + nta * ntb
   in case (eCh, cCh) of
        (C1, Ct) -> do
          eIdx <- idxOnesXY n1a nta n1b ntb aCh aI bCh bI
          Just (eIdx * ntc + cI)
        (Ct, C1) -> do
          eIdx <- idxTausXY n1a nta n1b ntb aCh aI bCh bI
          Just (n1ab * ntc + eIdx * n1c + cI)
        (Ct, Ct) -> do
          eIdx <- idxTausXY n1a nta n1b ntb aCh aI bCh bI
          Just (n1ab * ntc + ntab * n1c + eIdx * ntc + cI)
        _ -> Nothing

-- | Row in @a⊗(b⊗c)@ tau sector.
rightRowTaus
  :: Int -> Int -> Int -> Int -> Int -> Int
  -> Ch -> Int -> Ch -> Int -> Ch -> Int -> Ch
  -> Maybe Int
rightRowTaus n1a nta n1b ntb n1c ntc aCh aI bCh bI cCh cI fCh =
  let n1bc = n1b * n1c + ntb * ntc
      ntbc = n1b * ntc + ntb * n1c + ntb * ntc
   in case (aCh, fCh) of
        (C1, Ct) -> do
          fIdx <- idxTausXY n1b ntb n1c ntc bCh bI cCh cI
          Just (aI * ntbc + fIdx)
        (Ct, C1) -> do
          fIdx <- idxOnesXY n1b ntb n1c ntc bCh bI cCh cI
          Just (n1a * ntbc + aI * n1bc + fIdx)
        (Ct, Ct) -> do
          fIdx <- idxTausXY n1b ntb n1c ntc bCh bI cCh cI
          Just (n1a * ntbc + nta * n1bc + aI * ntbc + fIdx)
        _ -> Nothing

assocSectorEntries
  :: Bool -- ^ inverse F-symbols
  -> Ch -- ^ total charge
  -> ( Int -> Int -> Int -> Int -> Int -> Int
       -> Ch -> Int -> Ch -> Int -> Ch -> Int -> Ch
       -> Maybe Int
     ) -- ^ left column
  -> ( Int -> Int -> Int -> Int -> Int -> Int
       -> Ch -> Int -> Ch -> Int -> Ch -> Int -> Ch
       -> Maybe Int
     ) -- ^ right row
  -> Int -> Int -> Int -> Int -> Int -> Int
  -> [((Int, Int), Complex Double)]
assocSectorEntries inv total leftCol rightRow n1a nta n1b ntb n1c ntc =
  [ ((row, col), amp)
  | aCh <- [C1, Ct]
  , aI <- copiesOf aCh n1a nta
  , bCh <- [C1, Ct]
  , bI <- copiesOf bCh n1b ntb
  , cCh <- [C1, Ct]
  , cI <- copiesOf cCh n1c ntc
  , e <- [C1, Ct]
  , canFuse aCh bCh e
  , canFuse e cCh total
  , Just col <- [leftCol n1a nta n1b ntb n1c ntc aCh aI bCh bI cCh cI e]
  , (f, amp) <- fRow inv aCh bCh cCh total e
  , Just row <- [rightRow n1a nta n1b ntb n1c ntc aCh aI bCh bI cCh cI f]
  ]

buildAssocMatrix
  :: Bool
  -> Int -> Int -> Int -> Int -> Int -> Int
  -> (Int, Int)
  -> ( Int -> Int -> Int -> Int -> Int -> Int
       -> Ch -> Int -> Ch -> Int -> Ch -> Int -> Ch
       -> Maybe Int
     )
  -> ( Int -> Int -> Int -> Int -> Int -> Int
       -> Ch -> Int -> Ch -> Int -> Ch -> Int -> Ch
       -> Maybe Int
     )
  -> Ch
  -> LA.Matrix (Complex Double)
buildAssocMatrix inv n1a nta n1b ntb n1c ntc (nRows, nCols) leftCol rightRow total
  | nRows == 0 || nCols == 0 = LA.konst 0 (nRows, nCols)
  | otherwise =
      LA.accum (LA.konst 0 (nRows, nCols)) (+) $
        assocSectorEntries inv total leftCol rightRow n1a nta n1b ntb n1c ntc

-- | Associator @((a⊗b)⊗c) → (a⊗(b⊗c))@ on skeletal Hom via Fibonacci @F@-symbols.
-- Same @N@-basis order as 'tensorBlocks'.
associateBlocks
  :: forall n1a nta n1b ntb n1c ntc
   . KnownAssoc n1a nta n1b ntb n1c ntc
  => HomBlocks
      ( (n1a * n1b + nta * ntb) * n1c
          + ((n1a * ntb + nta * n1b) + nta * ntb) * ntc
      )
      ( ((n1a * n1b + nta * ntb) * ntc + ((n1a * ntb + nta * n1b) + nta * ntb) * n1c)
          + ((n1a * ntb + nta * n1b) + nta * ntb) * ntc
      )
      ( n1a * (n1b * n1c + ntb * ntc)
          + nta * ((n1b * ntc + ntb * n1c) + ntb * ntc)
      )
      ( (n1a * ((n1b * ntc + ntb * n1c) + ntb * ntc) + nta * (n1b * n1c + ntb * ntc))
          + nta * ((n1b * ntc + ntb * n1c) + ntb * ntc)
      )
associateBlocks =
  let n1a = natI @n1a
      nta = natI @nta
      n1b = natI @n1b
      ntb = natI @ntb
      n1c = natI @n1c
      ntc = natI @ntc
      n1ab = n1a * n1b + nta * ntb
      ntab = n1a * ntb + nta * n1b + nta * ntb
      n1bc = n1b * n1c + ntb * ntc
      ntbc = n1b * ntc + ntb * n1c + ntb * ntc
      n1L = n1ab * n1c + ntab * ntc
      ntL = n1ab * ntc + ntab * n1c + ntab * ntc
      n1R = n1a * n1bc + nta * ntbc
      ntR = n1a * ntbc + nta * n1bc + nta * ntbc
      oneBlk =
        buildAssocMatrix False n1a nta n1b ntb n1c ntc (n1R, n1L) leftColOnes rightRowOnes C1
      tauBlk =
        buildAssocMatrix False n1a nta n1b ntb n1c ntc (ntR, ntL) leftColTaus rightRowTaus Ct
   in HomBlocks (fromLA oneBlk) (fromLA tauBlk)

-- | Inverse associator via @F^{-1}@ (same basis).
disassociateBlocks
  :: forall n1a nta n1b ntb n1c ntc
   . KnownAssoc n1a nta n1b ntb n1c ntc
  => HomBlocks
      ( n1a * (n1b * n1c + ntb * ntc)
          + nta * ((n1b * ntc + ntb * n1c) + ntb * ntc)
      )
      ( (n1a * ((n1b * ntc + ntb * n1c) + ntb * ntc) + nta * (n1b * n1c + ntb * ntc))
          + nta * ((n1b * ntc + ntb * n1c) + ntb * ntc)
      )
      ( (n1a * n1b + nta * ntb) * n1c
          + ((n1a * ntb + nta * n1b) + nta * ntb) * ntc
      )
      ( ((n1a * n1b + nta * ntb) * ntc + ((n1a * ntb + nta * n1b) + nta * ntb) * n1c)
          + ((n1a * ntb + nta * n1b) + nta * ntb) * ntc
      )
disassociateBlocks =
  let n1a = natI @n1a
      nta = natI @nta
      n1b = natI @n1b
      ntb = natI @ntb
      n1c = natI @n1c
      ntc = natI @ntc
      n1ab = n1a * n1b + nta * ntb
      ntab = n1a * ntb + nta * n1b + nta * ntb
      n1bc = n1b * n1c + ntb * ntc
      ntbc = n1b * ntc + ntb * n1c + ntb * ntc
      n1L = n1ab * n1c + ntab * ntc
      ntL = n1ab * ntc + ntab * n1c + ntab * ntc
      n1R = n1a * n1bc + nta * ntbc
      ntR = n1a * ntbc + nta * n1bc + nta * ntbc
      -- Domain is right-associated; cols index @a⊗(b⊗c)@, rows @((a⊗b)⊗c)@.
      oneBlk =
        buildAssocMatrix True n1a nta n1b ntb n1c ntc (n1L, n1R) rightRowOnes leftColOnes C1
      tauBlk =
        buildAssocMatrix True n1a nta n1b ntb n1c ntc (ntL, ntR) rightRowTaus leftColTaus Ct
   in HomBlocks (fromLA oneBlk) (fromLA tauBlk)

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

-- | Pointwise equality on sector matrices (smoke checks / gallery).
eqFib :: (KnownMult a, KnownMult b) => Fib a b -> Fib a b -> Bool
eqFib (Fib (HomBlocks o1 t1)) (Fib (HomBlocks o2 t2)) =
  unwrap o1 == unwrap o2 && unwrap t1 == unwrap t2

-- | Zero morphism (both sectors).
zeroMor
  :: forall a c
   . (KnownMult a, KnownMult c)
  => Fib a c
zeroMor = Fib zeroBlocks

-- | @Fuse@ as a functor on morphisms: identity on Hom blocks.
--
-- Math: @Hom(a,b) ≅ Hom(Fuse a, Fuse b)@ already, so @fuseMap@ only reindexes
-- the object parameters. Laws: @fuseMap id = id@, @fuseMap (g ∘ f) = fuseMap g ∘ fuseMap f@.
fuseMap
  :: forall a b
   . (FuseIdemMult a, FuseIdemMult b)
  => Fib a b
  -> Fib (Fuse a) (Fuse b)
fuseMap (Fib h) = Fib h

--------------------------------------------------------------------------------
-- Category
--------------------------------------------------------------------------------

-- | Multiplicities known so @id@ \/ @(.)@ need no object-name table.
type FibObject a = KnownMult a

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
  (.) (Fib g) (Fib f) = Fib (composeBlocks g f)

--------------------------------------------------------------------------------
-- Tensor biendofunctor (tree layer)
--------------------------------------------------------------------------------

-- | @Tensor@ bifunctor: skeletal @N@-symbol Kronecker on Hom blocks
-- (@tensorBlocks@). Basis order matches @Norm@ distribute
-- (Ones from @𝟙⊗𝟙@ then @τ⊗τ→𝟙@; Taus from @𝟙⊗τ@, @τ⊗𝟙@, @τ⊗τ→τ@).
instance PFunctor Tensor Fib Fib where
  first
    :: forall a b c
     . ( Object Fib a
       , Object Fib b
       , Object Fib c
       , Object Fib (Tensor a c)
       , Object Fib (Tensor b c)
       )
    => Fib a b
    -> Fib (Tensor a c) (Tensor b c)
  first f = bimap f (id :: Fib c c)

instance QFunctor Tensor Fib Fib where
  second
    :: forall a b c
     . ( Object Fib a
       , Object Fib b
       , Object Fib c
       , Object Fib (Tensor c a)
       , Object Fib (Tensor c b)
       )
    => Fib a b
    -> Fib (Tensor c a) (Tensor c b)
  second g = bimap (id :: Fib c c) g

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
  bimap (Fib f) (Fib g) = Fib (tensorBlocks f g)

--------------------------------------------------------------------------------
-- Associative / Monoidal / Braided (Tensor)
--------------------------------------------------------------------------------

instance Associative Fib Tensor where
  associate
    :: forall a b c
     . ( Object Fib a
       , Object Fib b
       , Object Fib c
       , Object Fib (Tensor a b)
       , Object Fib (Tensor b c)
       , Object Fib (Tensor (Tensor a b) c)
       , Object Fib (Tensor a (Tensor b c))
       )
    => Fib (Tensor (Tensor a b) c) (Tensor a (Tensor b c))
  associate =
    Fib
      ( associateBlocks
          @(MultOne a)
          @(MultTau a)
          @(MultOne b)
          @(MultTau b)
          @(MultOne c)
          @(MultTau c)
      )

  disassociate
    :: forall a b c
     . ( Object Fib a
       , Object Fib b
       , Object Fib c
       , Object Fib (Tensor a b)
       , Object Fib (Tensor b c)
       , Object Fib (Tensor (Tensor a b) c)
       , Object Fib (Tensor a (Tensor b c))
       )
    => Fib (Tensor a (Tensor b c)) (Tensor (Tensor a b) c)
  disassociate =
    Fib
      ( disassociateBlocks
          @(MultOne a)
          @(MultTau a)
          @(MultOne b)
          @(MultTau b)
          @(MultOne c)
          @(MultTau c)
      )

instance Monoidal Fib Tensor where
  type Id Fib Tensor = 'One

  idl :: forall a. (Object Fib a, Object Fib 'One, Object Fib (Tensor 'One a)) => Fib (Tensor 'One a) a
  idl = Fib idBlocks

  idr :: forall a. (Object Fib a, Object Fib 'One, Object Fib (Tensor a 'One)) => Fib (Tensor a 'One) a
  idr = Fib idBlocks

  coidl :: forall a. (Object Fib a, Object Fib 'One, Object Fib (Tensor 'One a)) => Fib a (Tensor 'One a)
  coidl = Fib idBlocks

  coidr :: forall a. (Object Fib a, Object Fib 'One, Object Fib (Tensor a 'One)) => Fib a (Tensor a 'One)
  coidr = Fib idBlocks

instance Braided Fib Tensor where
  braid
    :: forall a b
     . ( Object Fib a
       , Object Fib b
       , Object Fib (Tensor a b)
       , Object Fib (Tensor b a)
       )
    => Fib (Tensor a b) (Tensor b a)
  braid = Fib (braidBlocks @(MultOne a) @(MultTau a) @(MultOne b) @(MultTau b))
