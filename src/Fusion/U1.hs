{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

-- | U(1) charge category as 'FusionTheory' \/ 'FusionData'.
--
-- Labels are 'Symmetry.Utils.Z' at the type level (@Label U1Th@); term labels are 'Integer'
-- charges. Fusion is charge addition (multiplicity 1); dual is negation.
-- Bosonic U(1): @F = 1@, @R = 1@, @cupCoeff = 1@.
module Fusion.U1
  ( U1Th
  ) where

import Data.Complex (Complex)
import Fusion.Data (FusionData (..))
import Fusion.Theory (FusionTheory (..), Label)
import Symmetry.Utils (Add, Negate, Z (..))

-- | Phantom tag for the U(1) fusion theory.
data U1Th

type instance Label U1Th = Z

instance FusionTheory Z U1Th where
  type UnitLab U1Th = 'Zero
  -- | @a ⊗ b ↦ Add a b@ with multiplicity 1.
  type FuseN U1Th a b = '[ '(Add a b, 1)]
  type DualLab U1Th j = Negate j

instance FusionData Z U1Th where
  type TermLab U1Th = Integer
  fuseOutcomes _ a b = [(a + b, 1)]
  fSymbol _ _inv a b c d e
    | e == a + b
    , let f = b + c
    , d == a + f
    , d == e + c =
        [(f, 1 :: Complex Double)]
    | otherwise = []
  rSymbol p a b c
    | nSymbol p a b c == 0 = 0
    | otherwise = 1
  cupCoeff _ _ = 1
