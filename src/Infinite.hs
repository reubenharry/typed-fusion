{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoStarIsType #-}

module Infinite where

import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import Data.VectorSpace.Free.FiniteSupportedSequence
import Data.Complex (Complex)
import GHC.TypeLits (KnownNat)
import Math.LinearMap.Category
  ( type (+>), type (⊗), LinearMap (..), Tensor (..), TensorSpace (..),
    AdditiveGroup (..), VectorSpace (..), Scalar, getLinearMap )
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Instances.Deriving ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Prelude hiding ((.), ($))
import Control.Category.Constrained.Prelude
import Numeric.LinearAlgebra.Static (C)

type Field = Complex Double
type Bond = FinSuppSeq Field

-- | Active support length of a bond vector (trailing zeros trimmed).
activeDimBond :: Bond -> Int
activeDimBond (FinSuppSeq v)
  | U.null v  = 0
  | otherwise = 1 + go (U.length v - 1)
  where
    go i
      | i < 0        = 0
      | v U.! i /= 0 = i + 1
      | otherwise    = go (i - 1)

-- | Shift bond-vector support right by @n@ slots (prepend zeros).
offsetBond :: Int -> Bond -> Bond
offsetBond 0 b = b
offsetBond n (FinSuppSeq v)
  | n <= 0    = FinSuppSeq v
  | otherwise = FinSuppSeq (U.replicate n 0 U.++ v)

type BondVec = V.Vector Bond

activeDimIntoBond :: BondVec -> Int
activeDimIntoBond = V.foldl' max 0 . V.map activeDimBond

offsetBondVec :: Int -> BondVec -> BondVec
offsetBondVec n = V.map (offsetBond n)

-- | Block-embed the second map's bond *output* after the first map's active dimension.
offsetCodomainIntoBond
  :: Int -> (C vp +> Bond) -> (C vp +> Bond)
offsetCodomainIntoBond n (LinearMap imgs) =
  LinearMap (offsetBondVec n imgs)

-- | Active bond dimension of a map whose domain is bond space.
activeDimFromBond :: [a] -> Int
activeDimFromBond = length

-- | Block-embed the second map's bond *input* after the first map's active dimension.
offsetDomainFromBond
  :: AdditiveGroup w => Int -> (Bond +> w) -> (Bond +> w)
offsetDomainFromBond n (LinearMap imgs) =
  LinearMap (replicate n zeroV ++ imgs)

-- | Offset the bond leg inside a physical ⊗ bond tensor.
offsetBondInTensor
  :: Int -> (C vp ⊗ Bond) -> (C vp ⊗ Bond)
offsetBondInTensor n (Tensor tp) = Tensor (V.map (offsetBond n) tp)

-- | Block-embed a center-site map on both bond input and bond output legs.
offsetCenterBond
  :: forall vp. KnownNat vp => Int -> (Bond +> (C vp ⊗ Bond)) -> (Bond +> (C vp ⊗ Bond))
offsetCenterBond n (LinearMap imgs) =
  LinearMap (replicate n zeroTensor ++ map (offsetBondInTensor n) imgs)

addIntoBond
  :: KnownNat vp => (C vp +> Bond) -> (C vp +> Bond) -> (C vp +> Bond)
addIntoBond f g =
  f ^+^ offsetCodomainIntoBond (activeDimIntoBond (getLinearMap f)) g

addFromBond
  :: (AdditiveGroup w, TensorSpace w, Scalar w ~ Field) =>
     (Bond +> w) -> (Bond +> w) -> (Bond +> w)
addFromBond f g =
  f ^+^ offsetDomainFromBond (activeDimFromBond (getLinearMap f)) g

addCenterMap
  :: forall vp. KnownNat vp =>
     (Bond +> (C vp ⊗ Bond)) -> (Bond +> (C vp ⊗ Bond)) -> (Bond +> (C vp ⊗ Bond))
addCenterMap f g =
  f ^+^ offsetCenterBond (activeDimFromBond (getLinearMap f)) g

data MPSClever vp = MPSClever
  { leftMPSClever  :: C vp +> Bond
  , center         :: Bond +> (C vp ⊗ Bond)
  , rightMPSClever :: Bond +> C vp
  }

zeroMPSClever :: KnownNat vp => MPSClever vp
zeroMPSClever = MPSClever zeroV zeroV zeroV

addMPSClever
  :: KnownNat vp => MPSClever vp -> MPSClever vp -> MPSClever vp
addMPSClever (MPSClever l c r) (MPSClever l' c' r') =
  MPSClever
    (addIntoBond l l')
    (addCenterMap c c')
    (addFromBond r r')

scaleMPSClever :: KnownNat vp => Field -> MPSClever vp -> MPSClever vp
scaleMPSClever μ (MPSClever l c r) =
  MPSClever (μ *^ l) (μ *^ c) (μ *^ r)

instance KnownNat vp => AdditiveGroup (MPSClever vp) where
  zeroV = zeroMPSClever
  (^+^) = addMPSClever
  negateV m = scaleMPSClever (-1) m

instance KnownNat vp => VectorSpace (MPSClever vp) where
  type Scalar (MPSClever vp) = Field
  μ *^ m = scaleMPSClever μ m

{-# DEPRECATED addClever "Use (^+^) on MPSClever instead" #-}
addClever :: KnownNat vp => MPSClever vp -> MPSClever vp -> MPSClever vp
addClever = addMPSClever
