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
-- (@t -> lab@). Term-level F\/R and fuse\/split live with each concrete
-- category (e.g. 'Experiments.Fibonacci').
module Experiments.Fusion.Theory
  ( FusionTheory (..)
  ) where

import Data.Kind (Type)
import GHC.TypeLits (Nat)

-- | @lab@: kind of simples. @t@: theory tag (determines @lab@).
class FusionTheory (lab :: Type) (t :: Type) | t -> lab where
  -- | Monoidal unit label.
  type UnitLab t :: lab
  -- | @N@-symbols: @a ⊗ b ≅ ⊕_c N_{ab}^c · c@.
  type FuseN t (a :: lab) (b :: lab) :: [(lab, Nat)]
