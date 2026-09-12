{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Term-level fusion data (N \/ F \/ R) for a theory tag.
module Fusion.Data
  ( FusionData (..)
  , fuseOutcomesFinite
  , LabVal (..)
  , allowedLeftMids
  , allowedRightMids
  ) where

import Data.Complex (Complex)
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Fusion.Theory (FiniteIrr (..), FusionTheory)
import Data.Maybe (fromMaybe)

-- | Promote a simple label to a term-level value (optional).
class LabVal (lab :: Type) (s :: lab) where
  labVal :: Proxy s -> lab

-- | Value-level structure constants.
-- @TermLab@ may differ from @code@ (e.g. SU(2): @code = Nat@, @TermLab = Int@).
--
-- Mathematical source for Hom cups \/ F \/ R scalars:
--
--   * 'cupCoeff' — cup\/ε factor on a simple (includes FS when the theory has it)
--   * 'fSymbol' — @[F^{abc}_d]_{e f}@ amplitudes
--   * 'rSymbol' — channel R-phase on @a ⊗ b → c@
class FusionTheory code t => FusionData (code :: Type) (t :: Type) | t -> code where
  type TermLab t :: Type
  fuseOutcomes :: Proxy t -> TermLab t -> TermLab t -> [(TermLab t, Int)]
  nSymbol :: Proxy t -> TermLab t -> TermLab t -> TermLab t -> Int
  default nSymbol
    :: Eq (TermLab t)
    => Proxy t
    -> TermLab t
    -> TermLab t
    -> TermLab t
    -> Int
  nSymbol p a b c = fromMaybe 0 (lookup c (fuseOutcomes p a b))
  canFuseD :: Proxy t -> TermLab t -> TermLab t -> TermLab t -> Bool
  canFuseD p a b c = nSymbol p a b c > 0
  fSymbol
    :: Proxy t
    -> Bool
    -> TermLab t
    -> TermLab t
    -> TermLab t
    -> TermLab t
    -> TermLab t
    -> [(TermLab t, Complex Double)]
  rSymbol :: Proxy t -> TermLab t -> TermLab t -> TermLab t -> Complex Double
  -- | Cup\/ε scalar on simple @j@ (SU(2): @FS(j)·dim(j)@; Fib: @d_τ = φ@ on τ).
  cupCoeff :: Proxy t -> TermLab t -> Complex Double

-- | @fuseOutcomes@ from 'irrVals' + 'nSymbol' when @TermLab t ~ code@.
fuseOutcomesFinite
  :: forall code t
   . (FiniteIrr code t, FusionData code t, TermLab t ~ code)
  => Proxy t
  -> code
  -> code
  -> [(code, Int)]
fuseOutcomesFinite p a b =
  [ (c, n)
  | c <- irrVals p
  , let n = nSymbol p a b c
  , n > 0
  ]

-- | Left intermediates @e@ for @((a⊗b)e)⊗c → d@.
allowedLeftMids
  :: FusionData code t
  => Proxy t
  -> TermLab t
  -> TermLab t
  -> TermLab t
  -> TermLab t
  -> [TermLab t]
allowedLeftMids p a b c d =
  [ e
  | (e, _) <- fuseOutcomes p a b
  , canFuseD p e c d
  ]

-- | Right intermediates @f@ for @a⊗((b⊗c)f) → d@.
allowedRightMids
  :: FusionData code t
  => Proxy t
  -> TermLab t
  -> TermLab t
  -> TermLab t
  -> TermLab t
  -> [TermLab t]
allowedRightMids p a b c d =
  [ f
  | (f, _) <- fuseOutcomes p b c
  , canFuseD p a f d
  ]
