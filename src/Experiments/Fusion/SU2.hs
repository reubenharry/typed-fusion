{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

-- | SU(2) representation category as 'FusionTheory' \/ 'FusionData'.
--
-- Type-level labels are @Nat@ (@2j@). Term-level @TermLab = Int@.
-- No 'FiniteIrr'. @rSymbol@ is the closed-form channel phase; @fSymbol@ (6j)
-- remains stubbed.
module Experiments.Fusion.SU2
  ( SU2Th
  , su2FuseOutcomes
  , su2RPhase
  ) where

import Data.Complex (Complex (..))
import Experiments.Fusion.Data (FusionData (..))
import Experiments.Fusion.Theory (FusionTheory (..))
import GHC.TypeLits (Nat)
import Symmetry.Tensor (TensorIrrepRepSU2)

data SU2Th

instance FusionTheory Nat SU2Th where
  type UnitLab SU2Th = 0
  type FuseN SU2Th j1 j2 = TensorIrrepRepSU2 j1 j2

su2FuseOutcomes :: Int -> Int -> [(Int, Int)]
su2FuseOutcomes j1 j2 =
  let lo = abs (j1 - j2)
      hi = j1 + j2
   in [ (j, 1) | j <- [lo, lo + 2 .. hi] ]

-- | Channel R-phase for bosonic SU(2): @(-1)^{j₁+j₂-j}@ with labels as @2j@.
-- Equivalent to the single-channel content of 'Symmetry.CG.RSymbol'.
su2RPhase :: Int -> Int -> Int -> Complex Double
su2RPhase tj1 tj2 tj
  | odd (tj1 + tj2 - tj) =
      error "su2RPhase: tj1+tj2-tj must be even (invalid fusion channel)"
  | even ((tj1 + tj2 - tj) `div` 2) = 1
  | otherwise = -1

instance FusionData Nat SU2Th where
  type TermLab SU2Th = Int
  fuseOutcomes _ = su2FuseOutcomes
  fSymbol _ _inv _a _b _c _d _e =
    error "Experiments.Fusion.SU2: fSymbol stub — wire to 6j / Symmetry.CG.FSymbol"
  rSymbol p a b c
    | nSymbol p a b c == 0 = 0
    | otherwise = su2RPhase a b c
  cupCoeff _ tj = fromIntegral (tj + 1) :+ 0
