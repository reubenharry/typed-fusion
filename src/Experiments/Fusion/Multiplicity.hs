{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

-- | Synthetic finite fusion theory with @N > 1@.
--
-- Labels @{𝟙, X}@ with
--
-- @
--   X ⊗ X  ≅  𝟙 ⊕ X ⊕ X     (N_{XX}^𝟙 = 1, N_{XX}^X = 2)
-- @
--
-- Demonstrates that 'FuseN' \/ 'fuseOutcomes' carry multiplicities.
-- @fSymbol@ \/ @rSymbol@ are filled for the multiplicity-free unitors and
-- unique channels; the @N=2@ @X@-channel uses a trivial (identity) F\/R on
-- the multiplicity space as a placeholder — a full pentagon-coherent choice
-- would need matrix-valued F on Hom spaces of dim @N@.
module Experiments.Fusion.Multiplicity
  ( MultTh
  , MultLab (..)
  ) where

import Data.Complex (Complex (..))
import Experiments.Fusion.Data (FusionData (..), fuseOutcomesFinite)
import Experiments.Fusion.Theory (FiniteIrr (..), FusionTheory (..))

data MultTh

-- | @{𝟙, X}@
data MultLab
  = MOne
  | MX
  deriving (Eq, Ord, Show)

instance FusionTheory MultLab MultTh where
  type UnitLab MultTh = 'MOne
  type FuseN MultTh 'MOne 'MOne = '[ '( 'MOne, 1)]
  type FuseN MultTh 'MOne 'MX = '[ '( 'MX, 1)]
  type FuseN MultTh 'MX 'MOne = '[ '( 'MX, 1)]
  -- | Nontrivial: two copies of @X@ in @X⊗X@.
  type FuseN MultTh 'MX 'MX = '[ '( 'MOne, 1), '( 'MX, 2)]
  type DualLab MultTh j = j

instance FiniteIrr MultLab MultTh where
  type Irr MultTh = '[ 'MOne, 'MX]
  irrVals _ = [MOne, MX]

instance FusionData MultLab MultTh where
  type TermLab MultTh = MultLab
  fuseOutcomes = fuseOutcomesFinite
  nSymbol _ MOne MOne MOne = 1
  nSymbol _ MOne MX MX = 1
  nSymbol _ MX MOne MX = 1
  nSymbol _ MX MX MOne = 1
  nSymbol _ MX MX MX = 2
  nSymbol _ _ _ _ = 0
  -- Multiplicity-free reassociations: amp 1. For total @X@ with @N=2@,
  -- return a single placeholder amp (scalar API cannot express Mat₂ yet).
  fSymbol p _ a b c d e =
    [ (f, 1)
    | f <- irrVals p
    , canFuseD p a b e
    , canFuseD p e c d
    , canFuseD p b c f
    , canFuseD p a f d
    ]
  rSymbol _ MX MX MOne = 1
  rSymbol _ MX MX MX = 1 -- placeholder on the 2-dim Hom
  rSymbol _ _ _ _ = 1
  cupCoeff _ MX = (1 + sqrt 2) :+ 0 -- d with d² = 1 + 2d
  cupCoeff _ _ = 1
