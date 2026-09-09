{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | Morphism-level Vect helpers used by 'Hom.Core'
-- (unitors, braid, associators, monoidal product of maps).
-- Extracted from the former TensorNetwork substrate — no MPS/DMRG.
module Categorical.Linear
  ( (⊗^)
  , swapMap
  , lassocMap
  , rassocMap
  , lunit
  , lunitInv
  , runit
  , runitInv
  ) where

import Prelude hiding (($), (.))
import Control.Arrow.Constrained (arr, ($))
import Control.Category.Constrained ((.))
import Data.Coerce (coerce)
import Data.Complex (Complex)
import Data.VectorSpace (Scalar)
import Math.LinearMap.Category
  ( LinearFunction
  , LinearSpace (..)
  , LSpace
  , Tensor (..)
  , TensorSpace (..)
  , applyDualVector
  , pattern LinearFunction
  , tensorOfMaps
  , type (+>)
  , type (⊗)
  , (⊗)
  , (-+$>)
  )
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Coercion (rassocTensor, (-+$=>))
import Math.OrphanInstances ()
import Numeric.LinearAlgebra.Static (C, Sized (konst))
import Numeric.LinearAlgebra.Static.COrphans ()

type ℂ = Complex Double

-- | Monoidal product of linear maps ('tensorOfMaps'):
--
--   @(f ⊗^ g) $ (x ⊗ y) = (f $ x) ⊗ (g $ y)@
(⊗^)
  :: forall u v u' v'
   . ( LSpace u, LSpace u', LSpace v, LSpace v'
     , TensorSpace v, TensorSpace v'
     , TensorSpace (u ⊗ u'), TensorSpace (v ⊗ v')
     , Scalar u ~ Scalar u', Scalar u ~ Scalar v, Scalar v ~ Scalar v'
     )
  => (u +> v) -> (u' +> v') -> ((u ⊗ u') +> (v ⊗ v'))
f ⊗^ g = (tensorOfMaps -+$> f) -+$> g
infixr 7 ⊗^

swapMap
  :: ( LinearSpace u, LinearSpace v
     , Scalar u ~ ℂ, Scalar v ~ ℂ )
  => (u ⊗ v) +> (v ⊗ u)
swapMap = arr transposeTensor

lassocMap
  :: ( LSpace u, LSpace v, LSpace w, Scalar u ~ Scalar v, Scalar v ~ Scalar w)
  => (u ⊗ (v ⊗ w)) +> ((u ⊗ v) ⊗ w)
lassocMap = arr $ LinearFunction coerce

rassocMap
  :: ( LinearSpace u, LinearSpace v, LinearSpace w
     , Scalar u ~ ℂ, Scalar v ~ ℂ, Scalar w ~ ℂ )
  => ((u ⊗ v) ⊗ w) +> (u ⊗ (v ⊗ w))
rassocMap = arr (LinearFunction (rassocTensor -+$=>))

oneC1 :: C 1
oneC1 = konst 1

scalarizeC1 :: LinearFunction ℂ (C 1) ℂ
scalarizeC1 = applyDualVector -+$> oneC1

runit
  :: forall v. (LinearSpace v, Scalar v ~ ℂ)
  => (v ⊗ C 1) +> v
runit = arr (fromFlatTensor . (fmapTensor -+$> scalarizeC1))

runitInv
  :: forall v. (LinearSpace v, Scalar v ~ ℂ)
  => v +> (v ⊗ C 1)
runitInv = arr (LinearFunction (\x -> x ⊗ oneC1))

lunit
  :: forall v. (LinearSpace v, Scalar v ~ ℂ, TensorSpace (C 1 ⊗ v))
  => (C 1 ⊗ v) +> v
lunit = runit . swapMap

lunitInv
  :: forall v. (LinearSpace v, Scalar v ~ ℂ, TensorSpace (C 1 ⊗ v))
  => v +> (C 1 ⊗ v)
lunitInv = swapMap . runitInv
