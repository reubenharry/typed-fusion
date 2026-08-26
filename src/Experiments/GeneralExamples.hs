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
import Numeric.LinearAlgebra.Static (Sized (fromList))
import Symmetry.Utils (Z (..))

--------------------------------------------------------------------------------
-- Coefficient comparison via 'HasBasis'
--------------------------------------------------------------------------------

approxEqCoeffs :: [Complex Double] -> [Complex Double] -> Bool
approxEqCoeffs xs ys =
  length xs == length ys
    && and (zipWith (\x y -> Complex.magnitude (x - y) < 1e-9) xs ys)

approxEqHasBasis
  :: (HasBasis v, Scalar v ~ Complex Double)
  => v
  -> v
  -> Bool
approxEqHasBasis u v =
  approxEqCoeffs (map snd (decompose u)) (map snd (decompose v))

--------------------------------------------------------------------------------
-- Smoke examples (singleton spines)
--------------------------------------------------------------------------------

fooMN :: Fuse U1 '[ '(Pos 2, Atom 2)] '[ '(Pos 2, Atom 2)]
fooMN =
  fuse @U1 @'[ '(Pos 2, Atom 2)] @'[ '(Pos 2, Atom 2)] $
    tensorSectors @U1 @(Pos 2) @2 @(Pos 2) @2
      (packAtomIrrep @2 @1 [fromList [3], fromList [5]])
      (packAtomIrrep @2 @1 [fromList [4], fromList [6]])

exRmoveMN_U1 :: BraidedFuse U1 '[ '(Pos 1, Atom 3)] '[ '(Pos 2, Atom 2)]
exRmoveMN_U1 =
  rmove @U1 @(Pos 1) @3 @(Pos 2) @2 $
    fuse @U1 @'[ '(Pos 1, Atom 3)] @'[ '(Pos 2, Atom 2)] $
      tensorSectors @U1 @(Pos 1) @3 @(Pos 2) @2
        (packAtomIrrep @3 @1 [fromList [3], fromList [3], fromList [3]])
        (packAtomIrrep @2 @1 [fromList [1], fromList [1]])

exRmoveMN_SU2 :: BraidedFuse SU2 '[ '(2, Atom 3)] '[ '(4, Atom 2)]
exRmoveMN_SU2 =
  rmove @SU2 @2 @3 @4 @2 $
    fuse @SU2 @'[ '(2, Atom 3)] @'[ '(4, Atom 2)] $
      tensorSectors @SU2 @2 @3 @4 @2
        (packAtomIrrep @3 @3
          [ fromList [1, 0, 0]
          , fromList [0, 1, 0]
          , fromList [0, 0, 1]
          ])
        (packAtomIrrep @2 @5
          [ fromList [1, 0, 0, 0, 0]
          , fromList [0, 1, 0, 0, 0]
          ])

--------------------------------------------------------------------------------
-- Coherence: fuse ∘ swap ≅ rmove ∘ fuse
--------------------------------------------------------------------------------

coherentRmoveMN
  :: forall g a m b n.
     ( KnownNat m
     , KnownNat n
     , KnownNat (IrrepDim g a)
     , KnownNat (IrrepDim g b)
     , UnfuseRaw g '[ '(a, Atom m)] '[ '(b, Atom n)]
         ~ '[UnfusePair g '(a, Atom m) '(b, Atom n)]
     , UnfuseRaw g '[ '(b, Atom n)] '[ '(a, Atom m)]
         ~ '[UnfusePair g '(b, Atom n) '(a, Atom m)]
     , CanFuse g '[ '(a, Atom m)] '[ '(b, Atom n)]
     , CanFuse g '[ '(b, Atom n)] '[ '(a, Atom m)]
     , CanRmove g a b (Tensor g '[ '(a, Atom m)] '[ '(b, Atom n)])
     , BraidReps g (Tensor g '[ '(a, Atom m)] '[ '(b, Atom n)])
         ~ Tensor g '[ '(b, Atom n)] '[ '(a, Atom m)]
     , HasBasis (BraidedFuse g '[ '(a, Atom m)] '[ '(b, Atom n)])
     , Scalar (BraidedFuse g '[ '(a, Atom m)] '[ '(b, Atom n)]) ~ Complex Double
     )
  => Unfuse g '[ '(a, Atom m)] '[ '(b, Atom n)]
  -> Bool
coherentRmoveMN unfused =
  approxEqHasBasis
    ( fuse @g @'[ '(b, Atom n)] @'[ '(a, Atom m)]
        (swapUnfuse @g @a @m @b @n unfused)
    )
    ( rmove @g @a @m @b @n
        (fuse @g @'[ '(a, Atom m)] @'[ '(b, Atom n)] unfused)
    )

exCoherenceRmoveMN_U1 :: Bool
exCoherenceRmoveMN_U1 =
  coherentRmoveMN @U1 @(Pos 1) @3 @(Pos 2) @2 $
    tensorSectors @U1 @(Pos 1) @3 @(Pos 2) @2
      (packAtomIrrep @3 @1 [fromList [3], fromList [3], fromList [3]])
      (packAtomIrrep @2 @1 [fromList [1], fromList [1]])

exCoherenceRmoveMN_SU2 :: Bool
exCoherenceRmoveMN_SU2 =
  coherentRmoveMN @SU2 @2 @3 @4 @2 $
    tensorSectors @SU2 @2 @3 @4 @2
      (packAtomIrrep @3 @3
        [ fromList [1, 0, 0]
        , fromList [0, 1, 0]
        , fromList [0, 0, 1]
        ])
      (packAtomIrrep @2 @5
        [ fromList [1, 0, 0, 0, 0]
        , fromList [0, 1, 0, 0, 0]
        ])

exCoherenceRmoveMN_SU2_leaf :: Bool
exCoherenceRmoveMN_SU2_leaf =
  coherentRmoveMN @SU2 @1 @1 @1 @1 $
    tensorSectors @SU2 @1 @1 @1 @1
      (asSector1 (Irrep (fromList [1, 0]) :: Irrep SU2 1))
      (asSector1 (Irrep (fromList [0, 1]) :: Irrep SU2 1))
