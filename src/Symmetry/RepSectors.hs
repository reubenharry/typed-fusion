{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Apply a same-spine intertwiner on 'RepToSectors': zip sectors and apply
-- @coeff ⊗ id@ on each multiplicity ⊗ irrep block.
module Symmetry.RepSectors
  ( ApplyEndoSectors (..)
  , ApplyHom (..)
  , applySector
  , intertwinerEndoSectors
  ) where

import Prelude hiding ((.), id, ($))
import Control.Arrow.Constrained (arr, ($))
import Control.Category.Constrained (id)
import Data.Complex (Complex)
import Data.VectorSpace (VectorSpace)
import GHC.TypeLits (KnownNat, Nat, type (*))
import Math.LinearMap.Category
  ( LSpace, LinearSpace, TensorSpace, type (⊗), type (+>), Scalar )
import Math.LinearMap.Asserted (linearFunction, type (-+>))
import Numeric.LinearAlgebra.Static (C)
import Numeric.LinearAlgebra.Static.COrphans ()
import TensorNetwork.Categorical ((⊗^))
import Symmetry.FunctorExperiment
  ( IntertwinerG (..)
  , IntertwinerSectorsG (..)
  )
import Symmetry.Group (Group (..), IntertwinerHom, IrrepDim, Irreps, Rep)
import Symmetry.HomBlock (CoeffBlock, HomBlockDim, applyBlock)
import Symmetry.RepObj (RepToSectors)

type ℂ = Complex Double

-- | @coeff ⊗ id@ on a multiplicity ⊗ irrep sector.
applySector
  :: forall m n d.
     ( KnownNat m, KnownNat n, KnownNat d
     , KnownNat (HomBlockDim m n)
     , HomBlockDim m n ~ (m * n)
     , LSpace (C n), LSpace (C m), LSpace (C d)
     , LSpace (C n ⊗ C d), LSpace (C m ⊗ C d)
     , TensorSpace (C n ⊗ C d), TensorSpace (C m ⊗ C d)
     , LinearSpace (C d)
     , Scalar (C n) ~ ℂ, Scalar (C m) ~ ℂ, Scalar (C d) ~ ℂ
     )
  => CoeffBlock m n
  -> (C n ⊗ C d)
  -> (C m ⊗ C d)
applySector blk v =
  (arr (linearFunction (applyBlock blk)) ⊗^ (id :: C d +> C d)) $ v

-- | Zip a hom-spine against a matching reduced spine.
class ApplyHom
      (g :: Group)
      (hom :: [(Irreps g, Nat, Nat)])
      (r :: Rep g) where
  applyHom
    :: IntertwinerSectorsG g hom
    -> RepToSectors g r
    -> RepToSectors g r

class ApplyHom g (IntertwinerHom g r r) r => ApplyEndoSectors (g :: Group) (r :: Rep g) where
  applyEndoSectors
    :: IntertwinerSectorsG g (IntertwinerHom g r r)
    -> RepToSectors g r
    -> RepToSectors g r

instance ApplyHom g (IntertwinerHom g r r) r => ApplyEndoSectors g r where
  applyEndoSectors = applyHom @g @(IntertwinerHom g r r) @r

intertwinerEndoSectors
  :: forall g r.
     ( ApplyEndoSectors g r
     , VectorSpace (RepToSectors g r)
     , Scalar (RepToSectors g r) ~ ℂ
     )
  => IntertwinerG g r r
  -> RepToSectors g r -+> RepToSectors g r
intertwinerEndoSectors (MkIntertwiner hom) =
  linearFunction (applyEndoSectors @g @r hom)

--------------------------------------------------------------------------------
-- SU(2)
--------------------------------------------------------------------------------

instance
  ( KnownNat j, KnownNat n, KnownNat (IrrepDim SU2 j)
  , LSpace (C n), LSpace (C (IrrepDim SU2 j))
  , LSpace (C n ⊗ C (IrrepDim SU2 j))
  , TensorSpace (C n ⊗ C (IrrepDim SU2 j))
  , LinearSpace (C (IrrepDim SU2 j))
  , Scalar (C n) ~ ℂ, Scalar (C (IrrepDim SU2 j)) ~ ℂ
  ) => ApplyHom SU2 '[ '(j, n, n)] '[ '(j, n)] where
  applyHom (InterCons blk InterNil) src =
    applySector @n @n @(IrrepDim SU2 j) blk src

instance
  ( KnownNat j, KnownNat n, KnownNat (IrrepDim SU2 j)
  , LSpace (C n), LSpace (C (IrrepDim SU2 j))
  , LSpace (C n ⊗ C (IrrepDim SU2 j))
  , TensorSpace (C n ⊗ C (IrrepDim SU2 j))
  , LinearSpace (C (IrrepDim SU2 j))
  , Scalar (C n) ~ ℂ, Scalar (C (IrrepDim SU2 j)) ~ ℂ
  , ApplyHom SU2 rest (s ': ss)
  ) => ApplyHom SU2 ('(j, n, n) ': rest) ('(j, n) ': s ': ss) where
  applyHom (InterCons blk homRest) (srcHead, srcRest) =
    ( applySector @n @n @(IrrepDim SU2 j) blk srcHead
    , applyHom @SU2 @rest @(s ': ss) homRest srcRest
    )

--------------------------------------------------------------------------------
-- U(1)
--------------------------------------------------------------------------------

instance
  ( KnownNat n, KnownNat (IrrepDim U1 z)
  , LSpace (C n), LSpace (C (IrrepDim U1 z))
  , LSpace (C n ⊗ C (IrrepDim U1 z))
  , TensorSpace (C n ⊗ C (IrrepDim U1 z))
  , LinearSpace (C (IrrepDim U1 z))
  , Scalar (C n) ~ ℂ, Scalar (C (IrrepDim U1 z)) ~ ℂ
  ) => ApplyHom U1 '[ '(z, n, n)] '[ '(z, n)] where
  applyHom (InterCons blk InterNil) src =
    applySector @n @n @(IrrepDim U1 z) blk src

instance
  ( KnownNat n, KnownNat (IrrepDim U1 z)
  , LSpace (C n), LSpace (C (IrrepDim U1 z))
  , LSpace (C n ⊗ C (IrrepDim U1 z))
  , TensorSpace (C n ⊗ C (IrrepDim U1 z))
  , LinearSpace (C (IrrepDim U1 z))
  , Scalar (C n) ~ ℂ, Scalar (C (IrrepDim U1 z)) ~ ℂ
  , ApplyHom U1 rest (s ': ss)
  ) => ApplyHom U1 ('(z, n, n) ': rest) ('(z, n) ': s ': ss) where
  applyHom (InterCons blk homRest) (srcHead, srcRest) =
    ( applySector @n @n @(IrrepDim U1 z) blk srcHead
    , applyHom @U1 @rest @(s ': ss) homRest srcRest
    )
