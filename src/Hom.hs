{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

-- | Symbolic SU(2): skeletal 'HomFused' objects and genealogy 'Rep' morphisms.
--
-- Layers: 'Fusion.Obj.Obj' → 'HomUnfused' / 'ToVObj'; skeletal
-- 'Spine' → 'HomFused' / 'HomInter' with 'RepV' / 'FuseRep' morphisms /
-- 'composeHomTrees' (HomInter: embed → compose → filter).
--
-- Hierarchy: 'Hom.Expr' (kinds),
-- 'Hom.TypeLevel' (families),
-- 'Hom.Singletons' / 'RepV' / 'FMove' / 'Core' (term-level),
-- 'Hom.Smoke' (concrete spines + checks).
-- Examples: 'Hom.Examples'.
-- Spines are spelled compositionally ('FuseRep', ''I', ''Atom') — no alias layer.
module Hom
  ( module Hom.Expr
  , module Hom.TypeLevel
  , module Hom.Singletons
  , module Hom.RepV
  , module Hom.FMove
  , module Hom.Core
  , module Hom.Smoke
  ) where

import Hom.Core
import Hom.Expr
import Hom.FMove
import Hom.RepV
import Hom.Singletons
import Hom.Smoke
import Hom.TypeLevel
