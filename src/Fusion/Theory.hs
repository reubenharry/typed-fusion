{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

-- | Fusion-theory interface (type level).
--
-- @Label t@ is the type of simple labels (@Label FibTh = Simple@, @Label SU2Th = Nat@, …).
-- The class still takes @lab@ with fundep @t -> lab@ so closed 'Obj' type families can
-- mention @lab@ without illegal type-family applications in equation heads
-- (@Label t@ cannot appear there). Prefer writing @Label t@ at call sites.
-- A complete list of simples is only on 'FiniteIrr'.
module Fusion.Theory
  ( Label
  , FusionTheory (..)
  , FiniteIrr (..)
  ) where

import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import GHC.TypeLits (Nat)

-- | Simple-label type of a theory tag.
--
-- Must agree with the @lab@ argument of 'FusionTheory' \/ 'FiniteIrr'
-- (@Label FibTh ~ Simple@, etc.). Kept as a standalone family so call sites can
-- write @Obj (Label t)@ without threading @lab@; not used in the *kinds* of
-- 'UnitLab' \/ 'FuseN' \/ 'DualLab' (those use the class parameter for Obj TF legality).
type family Label (t :: Type) :: Type

-- | Core fusion theory: unit + @N@-symbols + rigid dual on simples.
-- No complete @Irr@ list.
class FusionTheory (lab :: Type) (t :: Type) | t -> lab where
  type UnitLab t :: lab
  type FuseN t (a :: lab) (b :: lab) :: [(lab, Nat)]
  -- | Dual simple @j ↦ j^*@ (rigid structure on labels).
  type DualLab t (j :: lab) :: lab

-- | Finite fusion: complete ordered list of simples (Fib, Ising, …).
class FusionTheory lab t => FiniteIrr (lab :: Type) (t :: Type) | t -> lab where
  type Irr t :: [lab]
  irrVals :: Proxy t -> [lab]
  -- | Term-level unit label (matches 'UnitLab').
  unitVal :: Proxy t -> lab
