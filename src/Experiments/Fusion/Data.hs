{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Term-level fusion data (N \/ F \/ R) for a theory tag.
module Experiments.Fusion.Data
  ( FusionData (..)
  , LabVal (..)
  ) where

import Data.Complex (Complex)
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Experiments.Fusion.Theory (FusionTheory)

-- | Promote a simple label to a term-level value (optional; theories may omit).
class LabVal (lab :: Type) (s :: lab) where
  labVal :: Proxy s -> lab

-- | Value-level structure constants for a finite fusion theory.
class FusionTheory lab t => FusionData (lab :: Type) (t :: Type) | t -> lab where
  -- | All simples, same order as @Irr t@.
  irrVals :: Proxy t -> [lab]
  -- | @N_{ab}^c@ (0 if absent).
  nSymbol :: Proxy t -> lab -> lab -> lab -> Int
  -- | Whether @a ⊗ b → c@ is allowed (@N > 0@).
  canFuseD :: Proxy t -> lab -> lab -> lab -> Bool
  canFuseD p a b c = nSymbol p a b c > 0
  -- | @F^{abc}_{d; e → f}@ (@inv=False@) or @F^{-1}@ (@inv=True@).
  -- Returns amplitudes for each allowed right intermediate @f@.
  fSymbol
    :: Proxy t
    -> Bool
    -> lab
    -> lab
    -> lab
    -> lab
    -> lab
    -> [(lab, Complex Double)]
  -- | @R^{ab}_c@ braiding phase on channel @a ⊗ b → c@.
  rSymbol :: Proxy t -> lab -> lab -> lab -> Complex Double
  -- | Cup coefficient in the unit channel for a self-dual simple (theory-specific).
  cupCoeff :: Proxy t -> lab -> Complex Double
