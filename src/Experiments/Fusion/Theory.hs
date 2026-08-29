{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

-- | Fusion-theory interface (TensorKit-style @Sector@ data, type level).
--
-- @lab@ is the kind of simple labels; @t@ is a phantom theory tag
-- (@t -> lab@). Term-level F\/R live in 'Experiments.Fusion.Data'.
module Experiments.Fusion.Theory
  ( FusionTheory (..)
  , LabelEq
  ) where

import Data.Kind (Type)
import GHC.TypeLits (Nat)

-- | @lab@: kind of simples. @t@: theory tag (determines @lab@).
class FusionTheory (lab :: Type) (t :: Type) | t -> lab where
  -- | Monoidal unit label.
  type UnitLab t :: lab
  -- | Ordered list of simples (Hom sector order / Stabilize).
  type Irr t :: [lab]
  -- | @N@-symbols: @a ⊗ b ≅ ⊕_c N_{ab}^c · c@.
  type FuseN t (a :: lab) (b :: lab) :: [(lab, Nat)]

-- | Closed label equality (for unitors \/ multiplicity deltas).
type family LabelEq (a :: k) (b :: k) :: Bool where
  LabelEq a a = 'True
  LabelEq _ _ = 'False
