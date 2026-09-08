{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

-- | U(1) representation category as 'FusionTheory' \/ 'FusionData'.
--
-- Type-level charges are 'Symmetry.Utils.Z'. Term-level @TermLab = Integer@.
-- Fusion is additive and multiplicity-free; F\/R are trivial (bosonic).
module Experiments.Fusion.U1
  ( U1Th
  , u1FuseOutcomes
  ) where

import Experiments.Fusion.Data (FusionData (..))
import Experiments.Fusion.Theory (FusionTheory (..))
import Symmetry.Utils (Add, Negate, Z (..))

data U1Th

instance FusionTheory Z U1Th where
  type UnitLab U1Th = 'Zero
  type FuseN U1Th a b = '[ '(Add a b, 1)]
  type DualLab U1Th z = Negate z

u1FuseOutcomes :: Integer -> Integer -> [(Integer, Int)]
u1FuseOutcomes z1 z2 = [(z1 + z2, 1)]

instance FusionData Z U1Th where
  type TermLab U1Th = Integer
  fuseOutcomes _ = u1FuseOutcomes
  -- Unique fusion trees: amplitude 1 on the only allowed reassociation
  -- (F = F⁻¹ on U(1)).
  fSymbol p _ a b c d e =
    [ (f, 1)
    | (f, _) <- fuseOutcomes p b c
    , canFuseD p a f d
    , canFuseD p a b e
    , canFuseD p e c d
    ]
  rSymbol _ _ _ _ = 1
  cupCoeff _ _ = 1
