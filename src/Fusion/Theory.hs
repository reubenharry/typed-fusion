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
-- @code@ is the type of simple labels (@Simple@, @Nat@ for SU(2) @2j@, …).
-- A complete list of simples is only on 'FiniteIrr'.
module Fusion.Theory
  ( FusionTheory (..)
  , FiniteIrr (..)
  , LabelEq
  ) where

import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import GHC.TypeLits (Nat)

-- | Core fusion theory: unit + @N@-symbols + rigid dual on simples.
-- No complete @Irr@ list.
class FusionTheory (code :: Type) (t :: Type) | t -> code where
  type UnitLab t :: code
  type FuseN t (a :: code) (b :: code) :: [(code, Nat)]
  -- | Dual simple @j ↦ j^*@ (rigid structure on labels).
  type DualLab t (j :: code) :: code

-- | Finite fusion: complete ordered list of simples (Fib, Ising, …).
class FusionTheory code t => FiniteIrr (code :: Type) (t :: Type) | t -> code where
  type Irr t :: [code]
  irrVals :: Proxy t -> [code]

-- | Closed label equality (for unitors \/ multiplicity deltas).
type family LabelEq (a :: k) (b :: k) :: Bool where
  LabelEq a a = 'True
  LabelEq _ _ = 'False