{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

-- | Symbolic SU(2): skeletal 'HomFused' objects and genealogy 'FTree' morphisms.
--
-- Layers: 'Fusion.Obj.Obj' → 'HomUnfused' / 'ToVObj'; skeletal
-- 'Spine' → 'HomFused' / 'HomInter' with 'FTreeV' / 'FuseFTrees' morphisms /
-- 'composeHomTrees' (HomInter: embed → compose → filter).
--
-- Hierarchy: 'Hom.Expr' (kinds),
-- 'Hom.TypeLevel' (families),
-- 'Hom.Singletons' / 'FTreeV' / 'FMove' / 'Core' (term-level),
-- 'Hom.Smoke' (concrete spines + checks).
-- Examples: 'Examples.Symbolic'.
-- Spines are spelled compositionally ('FuseFTrees', ''IrrepTree', ''Irrep') — no alias layer.
module Hom
  ( module Hom.Expr
  , module Hom.TypeLevel
  , module Hom.Singletons
  , module Hom.FTreeV
  , module Hom.FMove
  , module Hom.Core
  , module Hom.Smoke
  ) where

import Hom.Core
import Hom.Expr
import Hom.FMove
import Hom.FTreeV
import Hom.Singletons
import Hom.Smoke
import Hom.TypeLevel
