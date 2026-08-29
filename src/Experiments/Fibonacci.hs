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
-- * __Hom__: sector matrices @HomBlocks@ on multiplicities @MultOne@ \/
--   @MultTau@ (@N@-bilinear on @'Tensor@, additive on @'Sum@).
-- * __Compose__: @composeBlocks@ (per-sector matrix multiply); @cup@ carries @φ@.
-- * __Fuse functor__: @fuseMap@ reindexes object parameters (id on blocks).
-- * __Tensor bifunctor__: @tensorBlocks@ \/ @tensorFib@ — Kronecker via @N@-symbols.
-- * __Monoidal \/ braided__: @Associative@\/@Monoidal@\/@Braided@ on @Tensor@
--   (@fmove@; @braidBlocks@\/@rmove@\/unitors; not 'Symmetric').
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
  , AssocL
  , AssocR
    -- * Hom
  , HomBlocks (..)
  , Fib (..)
  , SFib (..)
  , KnownFib (..)
  , sfTauTau
  , sfOnePlusTau
  , sfAssocL
  , sfAssocR
  , composeBlocks
  , idBlocks
  , zeroBlocks
  , tensorBlocks
  , braidBlocks
  , braidFib
  , phi
  , phiInv
  , phiInvSqrt
  , cup
  , cap
  , composeFib
  , zeroMor
  , fuseMap
  , tensorFib
    -- * Fuse \/ split
  , fuse
  , split
    -- * F \/ R
  , fmove
  , fmoveInv
  , rmove
  , rPhaseTauTauOne
  , rPhaseTauTauTau
    -- * Fusion theory
  , FibTh
  ) where

import Control.Category.Constrained.Prelude (Category (..))
import Data.Complex (Complex (..))
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
-- Singletons / objects of the category
--------------------------------------------------------------------------------

data SFib (a :: FibObj) where
  SFOne :: SFib 'One
  SFTau :: SFib 'Tau
  SFTensor :: SFib a -> SFib b -> SFib (Tensor a b)
  SFSum :: SFib a -> SFib b -> SFib (Sum a b)

class KnownFib (a :: FibObj) where
  fibSing :: SFib a

instance KnownFib 'One where fibSing = SFOne
instance KnownFib 'Tau where fibSing = SFTau
instance (KnownFib a, KnownFib b) => KnownFib (Tensor a b) where
  fibSing = SFTensor (fibSing @a) (fibSing @b)
instance (KnownFib a, KnownFib b) => KnownFib (Sum a b) where
  fibSing = SFSum (fibSing @a) (fibSing @b)

-- | Convenience singletons for common trees.
sfTauTau :: SFib TauTau
sfTauTau = SFTensor SFTau SFTau

sfOnePlusTau :: SFib OnePlusTau
sfOnePlusTau = SFSum SFOne SFTau

sfAssocL :: SFib AssocL
sfAssocL = SFTensor sfTauTau SFTau

sfAssocR :: SFib AssocR
sfAssocR = SFTensor SFTau sfTauTau


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
   . ( KnownNat n1x
     , KnownNat ntx
     , KnownNat n1y
     , KnownNat nty
     , KnownNat n1z
     , KnownNat ntz
     , KnownNat n1w
     , KnownNat ntw
     , KnownNat (n1x * n1z)
     , KnownNat (ntx * ntz)
     , KnownNat (n1y * n1w)
     , KnownNat (nty * ntw)
     , KnownNat (n1x * ntz)
     , KnownNat (ntx * n1z)
     , KnownNat (n1y * ntw)
     , KnownNat (nty * n1w)
     , KnownNat (n1x * n1z + ntx * ntz)
     , KnownNat (n1y * n1w + nty * ntw)
     , KnownNat (n1x * ntz + ntx * n1z)
     , KnownNat ((n1x * ntz + ntx * n1z) + ntx * ntz)
     , KnownNat (n1y * ntw + nty * n1w)
     , KnownNat ((n1y * ntw + nty * n1w) + nty * ntw)
     , KnownNat (n1x * n1z)
     , KnownNat (n1y * n1w)
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
rPhaseOneOne :: Complex Double
rPhaseOneOne = 1

rPhaseOneTau :: Complex Double
rPhaseOneTau = 1

rPhaseTauOne :: Complex Double
rPhaseTauOne = 1

-- | @R^{ττ}_𝟙 = e^{-4πi/5}@.
rPhaseTauTauOne :: Complex Double
rPhaseTauTauOne =
  let i = 0 :+ 1
   in exp (-4 * pi * i / 5)

-- | @R^{ττ}_τ = e^{3πi/5}@.
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
   . ( KnownNat n1a
     , KnownNat nta
     , KnownNat n1b
     , KnownNat ntb
     , KnownNat (n1a * n1b)
     , KnownNat (nta * ntb)
     , KnownNat (n1b * n1a)
     , KnownNat (ntb * nta)
     , KnownNat (n1a * ntb)
     , KnownNat (nta * n1b)
     , KnownNat (n1b * nta)
     , KnownNat (ntb * n1a)
     , KnownNat (n1a * n1b + nta * ntb)
     , KnownNat (n1b * n1a + ntb * nta)
     , KnownNat (n1a * ntb + nta * n1b)
     , KnownNat ((n1a * ntb + nta * n1b) + nta * ntb)
     , KnownNat (n1b * nta + ntb * n1a)
     , KnownNat ((n1b * nta + ntb * n1a) + ntb * nta)
     )
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
          [ [commuteKron n1a n1b rPhaseOneOne, LA.konst 0 (onesCod, nta * ntb)]
          , [LA.konst 0 (ntb * nta, onesDom), commuteKron nta ntb rPhaseTauTauOne]
          ]
      -- τ-sector rows = OT'|TO'|TT' (b⊗a), cols = OT|TO|TT (a⊗b):
      --   OT → TO' (R^{𝟙τ}), TO → OT' (R^{τ𝟙}), TT → TT' (R^{ττ}_τ).
      otToTo = commuteKron n1a ntb rPhaseOneTau
      toToOt = commuteKron nta n1b rPhaseTauOne
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

-- | Braiding @τ⊗τ → τ⊗τ@ in fused channels @(𝟙, τ)@.
--
-- Convention (Bonderson \/ Fibonacci anyons):
-- @R^{ττ}_𝟙 = e^{-4πi/5}@, @R^{ττ}_τ = e^{3πi/5}@ (see 'braidBlocks').
rmove :: Fib TauTau TauTau
rmove = braidFib @'Tau @'Tau

-- | Associator @(τ⊗τ)⊗τ → τ⊗(τ⊗τ)@ on the common fused spine
-- @Fuse = 𝟙 ⊕ τ ⊕ τ@ (@HomBlocks@: @1×1@ on 𝟙, @2×2@ on τ).
--
-- __τ-sector basis__ (both @AssocL@ and @AssocR@): after @FuseNorm@ one has
-- @Sum Tau (Sum One Tau)@, i.e. @CollectSimples = [τ, 𝟙, τ]@; @Stabilize@
-- sorts to @[𝟙, τ, τ]@. The τ-block indices are therefore
--
-- * @0@: intermediate @𝟙@ (vacuum channel of the first @τ⊗τ@ fuse),
-- * @1@: intermediate @τ@.
--
-- Matrices (standard unitary Fibonacci \/ Bonderson): @F^{τττ}_𝟙 = φ⁻¹@,
-- @F^{τττ}_τ@ as below. Pentagon\/hexagon not yet tested in-tree.
fmove :: Fib AssocL AssocR
fmove =
  Fib $
    HomBlocks
      (fromList [phiInv] :: M 1 1)
      ( fromList
          [ phiInv
          , phiInvSqrt
          , phiInvSqrt
          , -phiInv
          ] ::
          M 2 2
      )

-- | Inverse associator: @φ@ on the 𝟙-block; @F_τ@ is an involution.
fmoveInv :: Fib AssocR AssocL
fmoveInv =
  Fib $
    HomBlocks
      (fromList [phi] :: M 1 1)
      ( fromList
          [ phiInv
          , phiInvSqrt
          , phiInvSqrt
          , -phiInv
          ] ::
          M 2 2
      )

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

-- | Bifunctorial tensor on morphisms (@N@-symbol Kronecker).
tensorFib
  :: forall a b c d
   . ( KnownNat (MultOne a)
     , KnownNat (MultTau a)
     , KnownNat (MultOne b)
     , KnownNat (MultTau b)
     , KnownNat (MultOne c)
     , KnownNat (MultTau c)
     , KnownNat (MultOne d)
     , KnownNat (MultTau d)
     , KnownNat (MultOne a * MultOne c)
     , KnownNat (MultTau a * MultTau c)
     , KnownNat (MultOne b * MultOne d)
     , KnownNat (MultTau b * MultTau d)
     , KnownNat (MultOne a * MultTau c)
     , KnownNat (MultTau a * MultOne c)
     , KnownNat (MultOne b * MultTau d)
     , KnownNat (MultTau b * MultOne d)
     , KnownNat (MultOne a * MultOne c + MultTau a * MultTau c)
     , KnownNat (MultOne b * MultOne d + MultTau b * MultTau d)
     , KnownNat (MultOne a * MultTau c + MultTau a * MultOne c)
     , KnownNat ((MultOne a * MultTau c + MultTau a * MultOne c) + MultTau a * MultTau c)
     , KnownNat (MultOne b * MultTau d + MultTau b * MultOne d)
     , KnownNat ((MultOne b * MultTau d + MultTau b * MultOne d) + MultTau b * MultTau d)
     )
  => Fib a b
  -> Fib c d
  -> Fib (Tensor a c) (Tensor b d)
tensorFib (Fib f) (Fib g) = Fib (tensorBlocks f g)

-- | Braiding morphism @a⊗b → b⊗a@ via 'braidBlocks'.
braidFib
  :: forall a b
   . ( KnownNat (MultOne a)
     , KnownNat (MultTau a)
     , KnownNat (MultOne b)
     , KnownNat (MultTau b)
     , KnownNat (MultOne a * MultOne b)
     , KnownNat (MultTau a * MultTau b)
     , KnownNat (MultOne b * MultOne a)
     , KnownNat (MultTau b * MultTau a)
     , KnownNat (MultOne a * MultTau b)
     , KnownNat (MultTau a * MultOne b)
     , KnownNat (MultOne b * MultTau a)
     , KnownNat (MultTau b * MultOne a)
     , KnownNat (MultOne a * MultOne b + MultTau a * MultTau b)
     , KnownNat (MultOne b * MultOne a + MultTau b * MultTau a)
     , KnownNat (MultOne a * MultTau b + MultTau a * MultOne b)
     , KnownNat ((MultOne a * MultTau b + MultTau a * MultOne b) + MultTau a * MultTau b)
     , KnownNat (MultOne b * MultTau a + MultTau b * MultOne a)
     , KnownNat ((MultOne b * MultTau a + MultTau b * MultOne a) + MultTau b * MultTau a)
     )
  => Fib (Tensor a b) (Tensor b a)
braidFib = Fib (braidBlocks @(MultOne a) @(MultTau a) @(MultOne b) @(MultTau b))

--------------------------------------------------------------------------------
-- Category
--------------------------------------------------------------------------------

-- | Multiplicities known so @id@ \/ @(.)@ \/ @tensorFib@ need no object-name table.
-- @KnownFib@ enables @associate@\/@braid@ dispatch on concrete trees.
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

-- | @Tensor@ bifunctor: skeletal @N@-symbol Kronecker on Hom blocks
-- (@tensorBlocks@ \/ @tensorFib@). Basis order matches @Norm@ distribute
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
  first f = tensorFib f (id :: Fib c c)

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
  second g = tensorFib (id :: Fib c c) g

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
  bimap = tensorFib @a @b @c @d

--------------------------------------------------------------------------------
-- Associative / Monoidal / Braided (Tensor)
--------------------------------------------------------------------------------

associateBySing
  :: SFib a
  -> SFib b
  -> SFib c
  -> Fib (Tensor (Tensor a b) c) (Tensor a (Tensor b c))
associateBySing SFTau SFTau SFTau = fmove
associateBySing _ _ _ =
  error "Fib associate: general F-symbols not implemented (only τ⊗τ⊗τ; unit legs via idl/idr)"

disassociateBySing
  :: SFib a
  -> SFib b
  -> SFib c
  -> Fib (Tensor a (Tensor b c)) (Tensor (Tensor a b) c)
disassociateBySing SFTau SFTau SFTau = fmoveInv
disassociateBySing _ _ _ =
  error "Fib disassociate: general F-symbols not implemented (only τ⊗τ⊗τ; unit legs via idl/idr)"

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
  associate = associateBySing (fibSing @a) (fibSing @b) (fibSing @c)

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
  disassociate = disassociateBySing (fibSing @a) (fibSing @b) (fibSing @c)

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
  braid = braidFib @a @b
