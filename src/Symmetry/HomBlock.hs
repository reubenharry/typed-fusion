{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Hom blocks between matching-irrep sector copies.
--
-- By Schur, @Hom(V_j^{⊕n}, V_j^{⊕m}) ≅ M_{m,n}(C)@ for every compact group:
-- @m × n@ scalar coefficients, each acting as @λ · I@ on the irrep factor.
-- U(1) embeds those coefficients directly as @M m n@; SU(2) expands via
-- @kron(coeffMat, I_{j+1})@.
module Symmetry.HomBlock where

import Data.Vector.Storable (toList)
import GHC.TypeLits (Nat, KnownNat, natVal, type (*))
import Data.Proxy (Proxy (..))
import Numeric.LinearAlgebra.Static
  (C, M, konst, extract, Sized(fromList, unwrap), Domain(app, mul))
import qualified Numeric.LinearAlgebra as LA
import Numeric.LinearAlgebra.Static.COrphans ()  -- Eq (C n)
import Symmetry.Group (Group (..), Irreps, IrrepDim, SectorDim)

-- | Parameter count for a flat @U1HomBlock@ (coefficient layer).
type family HomBlockDim (m :: Nat) (n :: Nat) :: Nat where
  HomBlockDim m n = m * n

type family EndoHomDim (m :: Nat) :: Nat where
  EndoHomDim m = HomBlockDim m m

newtype U1HomBlock (m :: Nat) (n :: Nat) = U1HomBlock
  { unU1HomBlock :: M m n }

instance (KnownNat m, KnownNat n, KnownNat (m * n)) => Show (U1HomBlock m n) where
  show (U1HomBlock v) = show v

instance Eq (M m n) where
  a == b = undefined --  LA.flatten a == LA.flatten b

instance (KnownNat m, KnownNat n, KnownNat (m * n)) => Eq (U1HomBlock m n) where
  U1HomBlock a == U1HomBlock b = a == b

flattenMat
  :: forall m p d. (KnownNat m, KnownNat p, KnownNat d, HomBlockDim m p ~ d)
  => M m p -> C d
flattenMat mat = fromList $ LA.toList $ LA.flatten $ unwrap mat

u1BlockAsMat
  :: forall m n d. (KnownNat m, KnownNat n, KnownNat d, HomBlockDim m n ~ d)
  => U1HomBlock m n -> M m n
u1BlockAsMat (U1HomBlock block) = block --  fromList (toList (extract block))

u1ComposeBlock
  :: forall m n p d1 d2 d3.
     ( KnownNat m, KnownNat n, KnownNat p
     , KnownNat d1, KnownNat d2, KnownNat d3
     , HomBlockDim m n ~ d1, HomBlockDim n p ~ d2, HomBlockDim m p ~ d3 )
  => U1HomBlock m n -> U1HomBlock n p -> U1HomBlock m p
u1ComposeBlock ab bc = U1HomBlock (prod)
  where
    prod = mul (u1BlockAsMat ab) (u1BlockAsMat bc)

u1ZeroBlock
  :: forall m n. (KnownNat m, KnownNat n, KnownNat (HomBlockDim m n))
  => U1HomBlock m n
u1ZeroBlock = U1HomBlock (konst 0)

applyBlock
  :: forall m n d. (KnownNat m, KnownNat n, KnownNat d, HomBlockDim m n ~ d)
  => U1HomBlock m n -> C n -> C m
applyBlock blk = app (u1BlockAsMat blk)

applyEndoAt
  :: forall m h. (KnownNat m, KnownNat h, EndoHomDim m ~ h)
  => M m m -> C m -> C m
applyEndoAt block v = applyBlock (U1HomBlock block) v

su2ExpandBlock
  :: forall spin m n.
     (KnownNat spin, KnownNat m, KnownNat n, KnownNat (IrrepDim SU2 spin))
  => U1HomBlock m n -> M (SectorDim SU2 spin m) (SectorDim SU2 spin n)
su2ExpandBlock blk =
  fromList $
    LA.toList $
      LA.flatten $
        LA.kronecker
          (unwrap (u1BlockAsMat blk))
          (LA.ident (fromIntegral (natVal (Proxy @(IrrepDim SU2 spin)))))

--------------------------------------------------------------------------------
-- Group-indexed hom blocks
--------------------------------------------------------------------------------

class HasHomBlock (g :: Group) where
  type HomBlockDimG g (j :: Irreps g) (m :: Nat) (n :: Nat) :: Nat
  data HomBlock g (j :: Irreps g) (m :: Nat) (n :: Nat)

  zeroBlock
    :: (KnownNat m, KnownNat n, KnownNat (HomBlockDimG g j m n))
    => HomBlock g j m n

  wrapCoeffs
    :: (KnownNat m, KnownNat n, KnownNat (HomBlockDimG g j m n))
    => U1HomBlock m n -> HomBlock g j m n

  composeBlock
    :: forall j m n p.
       ( KnownNat m, KnownNat n, KnownNat p
       , KnownNat (HomBlockDimG g j m n)
       , KnownNat (HomBlockDimG g j n p)
       , KnownNat (HomBlockDimG g j m p)
       )
    => HomBlock g j m n -> HomBlock g j n p -> HomBlock g j m p

  blockAsMat
    :: forall j m n sm sn.
       ( KnownNat m, KnownNat n
       , KnownNat sm, KnownNat sn
       , sm ~ SectorDim g j m, sn ~ SectorDim g j n
       , KnownNat (HomBlockDimG g j m n)
       , KnownNat (IrrepDim g j)
       )
    => HomBlock g j m n -> M sm sn

instance HasHomBlock U1 where
  type HomBlockDimG U1 j m n = m * n
  newtype HomBlock U1 (j :: Irreps U1) (m :: Nat) (n :: Nat)
    = U1HB (U1HomBlock m n)

  zeroBlock = U1HB u1ZeroBlock
  wrapCoeffs = U1HB
  composeBlock (U1HB ab) (U1HB bc) = U1HB (u1ComposeBlock ab bc)
  blockAsMat (U1HB blk) = u1BlockAsMat blk

deriving instance
  ( KnownNat m, KnownNat n, KnownNat (HomBlockDimG U1 j m n)
  ) => Show (HomBlock U1 j m n)

deriving instance
  ( KnownNat m, KnownNat n, KnownNat (HomBlockDimG U1 j m n)
  ) => Eq (HomBlock U1 j m n)

instance HasHomBlock SU2 where
  type HomBlockDimG SU2 j m n = m * n
  newtype HomBlock SU2 (j :: Nat) (m :: Nat) (n :: Nat)
    = SU2HB (U1HomBlock m n)

  zeroBlock = SU2HB u1ZeroBlock
  wrapCoeffs = SU2HB
  composeBlock (SU2HB ab) (SU2HB bc) = SU2HB (u1ComposeBlock ab bc)
  blockAsMat (blk :: HomBlock SU2 j m n) =
    case blk of
      SU2HB b ->
        fromList $
          LA.toList $
            LA.flatten $
              LA.kronecker
                (unwrap (u1BlockAsMat b))
                (LA.ident (fromIntegral (natVal (Proxy @(IrrepDim SU2 j)))))

deriving instance
  ( KnownNat m, KnownNat n, KnownNat (HomBlockDimG SU2 j m n)
  ) => Show (HomBlock SU2 j m n)

deriving instance
  ( KnownNat m, KnownNat n, KnownNat (HomBlockDimG SU2 j m n)
  ) => Eq (HomBlock SU2 j m n)
