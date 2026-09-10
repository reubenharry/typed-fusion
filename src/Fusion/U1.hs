{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

-- | U(1) charge category as 'FusionTheory'.
--
-- Labels are 'Symmetry.Utils.Z'. Fusion is charge addition (multiplicity 1);
-- dual is charge negation.
module Fusion.U1
  ( U1Th
  ) where

import Fusion.Theory (FusionTheory (..))
import Symmetry.Utils (Add, Negate, Z (..))

-- | Phantom tag for the U(1) fusion theory.
data U1Th

instance FusionTheory Z U1Th where
  type UnitLab U1Th = 'Zero
  -- | @a ⊗ b ↦ Add a b@ with multiplicity 1.
  type FuseN U1Th a b = '[ '(Add a b, 1)]
  type DualLab U1Th j = Negate j
