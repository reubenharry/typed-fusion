{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Examples and coherence checks for 'Experiments.General'.
module Experiments.GeneralExamples where

import Data.Basis (HasBasis (..))
import Data.Complex (Complex (..))
import qualified Data.Complex as Complex
import Data.VectorSpace (Scalar)
import Experiments.General
import GHC.TypeLits (KnownNat)
import Math.LinearMap.Category (type (⊗))
import Numeric.LinearAlgebra.Static (C, Sized (fromList))
import Symmetry.Utils (Z (..))

--------------------------------------------------------------------------------
-- Coefficient comparison via 'HasBasis'
--------------------------------------------------------------------------------

approxEqCoeffs :: [Complex Double] -> [Complex Double] -> Bool
approxEqCoeffs xs ys =
  length xs == length ys
    && and (zipWith (\x y -> Complex.magnitude (x - y) < 1e-9) xs ys)

-- | Compare two vectors by their 'decompose' coefficient lists (stable basis order).
approxEqHasBasis
  :: (HasBasis v, Scalar v ~ Complex Double)
  => v
  -> v
  -> Bool
approxEqHasBasis u v =
  approxEqCoeffs (map snd (decompose u)) (map snd (decompose v))

--------------------------------------------------------------------------------
-- Smoke examples
--------------------------------------------------------------------------------

fooMN :: FuseMN U1 '(Pos 2, 2) '(Pos 2, 2)
fooMN =
  fuseMN @U1 @'(Pos 2, 2) @'(Pos 2, 2) $
    tensorSectors @U1 @(Pos 2) @2 @(Pos 2) @2
      (packMultIrrep @2 @1 [fromList [3], fromList [5]])
      (packMultIrrep @2 @1 [fromList [4], fromList [6]])

exRmoveMN_U1 :: FuseMN U1 '(Pos 1, 2) '(Pos 2, 3)
exRmoveMN_U1 =
  rmoveMN @U1 @'(Pos 2, 3) @'(Pos 1, 2) @(FuseSectors U1 '(Pos 2, 3) '(Pos 1, 2)) $
    fuseMN @U1 @'(Pos 2, 3) @'(Pos 1, 2) $
      tensorSectors @U1 @(Pos 2) @3 @(Pos 1) @2
        (packMultIrrep @3 @1 [fromList [3], fromList [3], fromList [3]])
        (packMultIrrep @2 @1 [fromList [1], fromList [1]])

exRmoveMN_SU2 :: FuseMN SU2 '(2, 3) '(4, 2)
exRmoveMN_SU2 =
  rmoveMN @SU2 @'(4, 2) @'(2, 3) @(FuseSectors SU2 '(4, 2) '(2, 3)) $
    fuseMN @SU2 @'(4, 2) @'(2, 3) $
      tensorSectors @SU2 @4 @2 @2 @3
        (packMultIrrep @2 @5
          [ fromList [1, 0, 0, 0, 0]
          , fromList [0, 1, 0, 0, 0]
          ])
        (packMultIrrep @3 @3
          [ fromList [1, 0, 0]
          , fromList [0, 1, 0]
          , fromList [0, 0, 1]
          ])

--------------------------------------------------------------------------------
-- Coherence: fuseMN ∘ swap ≅ rmoveMN ∘ fuseMN
--------------------------------------------------------------------------------

coherentRmoveMN
  :: forall g a m b n.
     ( KnownNat m
     , KnownNat n
     , KnownNat (IrrepDim g a)
     , KnownNat (IrrepDim g b)
     , Sector g a m ~ (C m ⊗ C (IrrepDim g a))
     , Sector g b n ~ (C n ⊗ C (IrrepDim g b))
     , CanFuseMN g '(a, m) '(b, n)
     , CanFuseMN g '(b, n) '(a, m)
     , CanRmoveMN g '(a, m) '(b, n) (FuseSectors g '(a, m) '(b, n))
     , FuseSectors g '(a, m) '(b, n) ~ FuseSectors g '(b, n) '(a, m)
     , HasBasis (FuseMN g '(b, n) '(a, m))
     , Scalar (FuseMN g '(b, n) '(a, m)) ~ Complex Double
     )
  => UnfuseMN g '(a, m) '(b, n)
  -> Bool
coherentRmoveMN unfused =
  approxEqHasBasis
    (fuseMN @g @'(b, n) @'(a, m) (swapUnfuseMN @g @a @m @b @n unfused))
    (rmoveMN @g @'(a, m) @'(b, n) @(FuseSectors g '(a, m) '(b, n))
      (fuseMN @g @'(a, m) @'(b, n) unfused))

exCoherenceRmoveMN_U1 :: Bool
exCoherenceRmoveMN_U1 =
  coherentRmoveMN @U1 @(Pos 1) @3 @(Pos 2) @2 $
    tensorSectors @U1 @(Pos 1) @3 @(Pos 2) @2
      (packMultIrrep @3 @1 [fromList [3], fromList [3], fromList [3]])
      (packMultIrrep @2 @1 [fromList [1], fromList [1]])

exCoherenceRmoveMN_SU2 :: Bool
exCoherenceRmoveMN_SU2 =
  coherentRmoveMN @SU2 @2 @3 @4 @2 $
    tensorSectors @SU2 @2 @3 @4 @2
      (packMultIrrep @3 @3
        [ fromList [1, 0, 0]
        , fromList [0, 1, 0]
        , fromList [0, 0, 1]
        ])
      (packMultIrrep @2 @5
        [ fromList [1, 0, 0, 0, 0]
        , fromList [0, 1, 0, 0, 0]
        ])

exCoherenceRmoveMN_SU2_leaf :: Bool
exCoherenceRmoveMN_SU2_leaf =
  coherentRmoveMN @SU2 @1 @1 @1 @1 $
    tensorSectors @SU2 @1 @1 @1 @1
      (asSector1 (Irrep (fromList [1, 0]) :: Irrep SU2 1))
      (asSector1 (Irrep (fromList [0, 1]) :: Irrep SU2 1))
