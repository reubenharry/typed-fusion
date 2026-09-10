{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

-- | Symbolic Hom(@g :: Group@): 'HomUnfused' / 'HomFused' / 'HomInter'.
--
-- Layers: 'Fusion.Obj.Obj' → 'HomUnfused' / 'ToVObj'; skeletal
-- 'Spine' → 'HomFused' / 'HomInter' with 'FTreeV' / 'FuseFTrees' morphisms /
-- 'composeHomTrees' (HomInter: embed → compose → filter).
-- SU(2) owns the Nat genealogy engine; U(1) has type-level fuse + runnable HomUnfused.
--
-- Hierarchy: 'Hom.Expr' (kinds),
-- 'Hom.TypeLevel' (families),
-- 'Hom.Singletons' / 'FTreeV' / 'FMove' / 'Core' (term-level),
-- 'Hom.Smoke' (concrete SU(2) spines + checks).
-- Examples: 'Examples.Symbolic'.
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
