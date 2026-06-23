{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

-- | One hom block between two sector copies: by Schur, an intertwiner restricted
-- to a single charge is an @m × n@ matrix of scalars. This module is the matrix
-- layer underneath 'FunctorExperiment.Intertwiner' — block storage and the
-- multiply\/apply\/zero operations on it — with no charge bookkeeping.
--
-- 'HomBlockDim' is the one knob a non-abelian (SU(2)) generalization turns: the
-- per-pair fiber is @m * n@ for U(1), larger otherwise.
module Symmetry.HomBlock
  ( HomBlockDim, EndoHomDim
  , U1HomBlock(..)
  , flattenMat, blockAsMat
  , composeBlock, zeroBlock, applyBlock, applyEndoAt
  ) where

import Data.Vector.Storable (toList)
import GHC.TypeLits (Nat, KnownNat, type (*))
import Numeric.LinearAlgebra.Static
  (C, M, konst, extract, Sized(fromList, unwrap), Domain(app, mul))
import qualified Numeric.LinearAlgebra as LA
import Numeric.LinearAlgebra.Static.COrphans ()  -- Eq (C n)

-- | Parameter count for a hom block between @m@ and @n@ sector copies.
type family HomBlockDim (m :: Nat) (n :: Nat) :: Nat where
  HomBlockDim m n = m * n

-- | Block dimension for an @m@-fold sector endomorphism.
type family EndoHomDim (m :: Nat) :: Nat where
  EndoHomDim m = HomBlockDim m m

-- | One hom block, stored as a flat @C (HomBlockDim m n)@ vector.
newtype U1HomBlock (m :: Nat) (n :: Nat) = U1HomBlock
  { unU1HomBlock :: C (HomBlockDim m n) }

instance (KnownNat m, KnownNat n, KnownNat (m * n)) => Show (U1HomBlock m n) where
  show (U1HomBlock v) = show v

instance (KnownNat m, KnownNat n, KnownNat (m * n)) => Eq (U1HomBlock m n) where
  U1HomBlock a == U1HomBlock b = a == b

-- | Pack a matrix into row-major flat block storage.
flattenMat
  :: forall m p d. (KnownNat m, KnownNat p, KnownNat d, HomBlockDim m p ~ d)
  => M m p -> C d
flattenMat mat = fromList $ LA.toList $ LA.flatten $ unwrap mat

-- | View a flat hom block as an @m × n@ matrix.
blockAsMat
  :: forall m n d. (KnownNat m, KnownNat n, KnownNat d, HomBlockDim m n ~ d)
  => U1HomBlock m n -> M m n
blockAsMat (U1HomBlock block) = fromList (toList (extract block))

-- | Compose blocks as matrix multiplication: @(m×n) . (n×p) = (m×p)@.
composeBlock
  :: forall m n p d1 d2 d3.
     ( KnownNat m, KnownNat n, KnownNat p
     , KnownNat d1, KnownNat d2, KnownNat d3
     , HomBlockDim m n ~ d1, HomBlockDim n p ~ d2, HomBlockDim m p ~ d3 )
  => U1HomBlock m n -> U1HomBlock n p -> U1HomBlock m p
composeBlock ab bc = U1HomBlock (flattenMat @m @p @d3 prod)
  where
    prod :: M m p
    prod = mul (blockAsMat ab) (blockAsMat bc)

-- | The zero block of a given shape.
zeroBlock
  :: forall m n. (KnownNat m, KnownNat n, KnownNat (HomBlockDim m n))
  => U1HomBlock m n
zeroBlock = U1HomBlock (konst 0)

-- | Apply an @m × n@ hom block to a source sector vector @C n@.
applyBlock
  :: forall m n d. (KnownNat m, KnownNat n, KnownNat d, HomBlockDim m n ~ d)
  => U1HomBlock m n -> C n -> C m
applyBlock blk = app (blockAsMat blk)

-- | Apply an @m@-fold endomorphism block (stored flat) to a sector vector.
applyEndoAt
  :: forall m h. (KnownNat m, KnownNat h, EndoHomDim m ~ h)
  => C h -> C m -> C m
applyEndoAt block v = applyBlock (U1HomBlock block) v
