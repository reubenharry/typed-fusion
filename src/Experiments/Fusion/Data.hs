{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Term-level fusion data (N \/ F \/ R) for a theory tag.
module Experiments.Fusion.Data
  ( FusionData (..)
  , fuseOutcomesFinite
  , LabVal (..)
  ) where

import Data.Complex (Complex)
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Experiments.Fusion.Theory (FiniteIrr (..), FusionTheory)

-- | Promote a simple label to a term-level value (optional).
class LabVal (lab :: Type) (s :: lab) where
  labVal :: Proxy s -> lab

-- | Value-level structure constants.
-- @TermLab@ may differ from @code@ (e.g. SU(2): @code = Nat@, @TermLab = Int@).
class FusionTheory code t => FusionData (code :: Type) (t :: Type) | t -> code where
  type TermLab t :: Type
  fuseOutcomes :: Proxy t -> TermLab t -> TermLab t -> [(TermLab t, Int)]
  nSymbol :: Proxy t -> TermLab t -> TermLab t -> TermLab t -> Int
  default nSymbol
    :: Eq (TermLab t)
    => Proxy t
    -> TermLab t
    -> TermLab t
    -> TermLab t
    -> Int
  nSymbol p a b c =
    case lookup c (fuseOutcomes p a b) of
      Just n -> n
      Nothing -> 0
  canFuseD :: Proxy t -> TermLab t -> TermLab t -> TermLab t -> Bool
  canFuseD p a b c = nSymbol p a b c > 0
  fSymbol
    :: Proxy t
    -> Bool
    -> TermLab t
    -> TermLab t
    -> TermLab t
    -> TermLab t
    -> TermLab t
    -> [(TermLab t, Complex Double)]
  rSymbol :: Proxy t -> TermLab t -> TermLab t -> TermLab t -> Complex Double
  cupCoeff :: Proxy t -> TermLab t -> Complex Double

-- | @fuseOutcomes@ from 'irrVals' + 'nSymbol' when @TermLab t ~ code@.
fuseOutcomesFinite
  :: forall code t
   . (FiniteIrr code t, FusionData code t, TermLab t ~ code)
  => Proxy t
  -> code
  -> code
  -> [(code, Int)]
fuseOutcomesFinite p a b =
  [ (c, n)
  | c <- irrVals p
  , let n = nSymbol p a b c
  , n > 0
  ]
