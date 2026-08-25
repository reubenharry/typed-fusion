{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Examples and coherence checks for 'Experiments.General'.
module Experiments.GeneralExamples where

import Data.Complex (Complex (..))
import qualified Data.Complex as Complex
import Experiments.Experiment2 (Multiplicity)
import Experiments.General
import GHC.TypeLits (KnownNat)
import Math.LinearMap.Category (type (⊗))
import Math.VectorSpace.DimensionAware (toArray)
import Numeric.LinearAlgebra.Static (C, Sized (fromList))
import Symmetry.Utils (HList (..), Z (..))
import qualified Data.Vector.Storable as VS

--------------------------------------------------------------------------------
-- Coefficient comparison (tests only)
--------------------------------------------------------------------------------

class FoldRepCoeffs g (rs :: [(Irreps g, Multiplicity)]) where
  foldRepCoeffs :: HList (RepToVectors g rs) -> [Complex Double]

instance FoldRepCoeffs U1 '[] where
  foldRepCoeffs HNil = []

instance FoldRepCoeffs SU2 '[] where
  foldRepCoeffs HNil = []

instance
  ( KnownNat m
  , FoldRepCoeffs U1 rs
  ) =>
  FoldRepCoeffs U1 ('(j, m) ': rs)
  where
  foldRepCoeffs (sec :& rest) =
    VS.toList (toArray sec :: VS.Vector (Complex Double))
      ++ foldRepCoeffs @U1 @rs rest

instance
  ( KnownNat j
  , KnownNat m
  , KnownNat (IrrepDim SU2 j)
  , FoldRepCoeffs SU2 rs
  ) =>
  FoldRepCoeffs SU2 ('(j, m) ': rs)
  where
  foldRepCoeffs (sec :& rest) =
    VS.toList (toArray sec :: VS.Vector (Complex Double))
      ++ foldRepCoeffs @SU2 @rs rest

approxEqCoeffs :: [Complex Double] -> [Complex Double] -> Bool
approxEqCoeffs xs ys =
  length xs == length ys
    && and (zipWith (\x y -> Complex.magnitude (x - y) < 1e-9) xs ys)

--------------------------------------------------------------------------------
-- Smoke examples
--------------------------------------------------------------------------------

fooMN :: FuseMN U1 '(Pos 2, 2) '(Pos 2, 2)
fooMN =
  fuseMN $
    tensorSectors
      (packMultIrrep @2 @1 [fromList [3], fromList [5]])
      (packMultIrrep @2 @1 [fromList [4], fromList [6]])

exRmoveMN_U1 :: FuseMN U1 '(Pos 1, 2) '(Pos 2, 3)
exRmoveMN_U1 =
  rmoveMN $
    fuseMN $
      tensorSectors
        (packMultIrrep @3 @1 [fromList [3], fromList [3], fromList [3]])
        (packMultIrrep @2 @1 [fromList [1], fromList [1]])

exRmoveMN_SU2 :: FuseMN SU2 '(2, 3) '(4, 2)
exRmoveMN_SU2 =
  rmoveMN $
    fuseMN $
      tensorSectors
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
     , CanRmoveMN g '(a, m) '(b, n)
     , FoldRepCoeffs g (FuseSectors g '(b, n) '(a, m))
     )
  => UnfuseMN g '(a, m) '(b, n)
  -> Bool
coherentRmoveMN unfused =
  let lhs = fuseMN (swapUnfuseMN unfused)
      rhs = rmoveMN (fuseMN unfused)
  in  approxEqCoeffs
        (foldRepCoeffs @g @(FuseSectors g '(b, n) '(a, m)) (unFuseMN lhs))
        (foldRepCoeffs @g @(FuseSectors g '(b, n) '(a, m)) (unFuseMN rhs))

exCoherenceRmoveMN_U1 :: Bool
exCoherenceRmoveMN_U1 =
  coherentRmoveMN @U1 @(Pos 1) @3 @(Pos 2) @2 $
    tensorSectors
      (packMultIrrep @3 @1 [fromList [3], fromList [3], fromList [3]])
      (packMultIrrep @2 @1 [fromList [1], fromList [1]])

exCoherenceRmoveMN_SU2 :: Bool
exCoherenceRmoveMN_SU2 =
  coherentRmoveMN @SU2 @2 @3 @4 @2 $
    tensorSectors
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
    tensorSectors
      (asSector1 (Irrep (fromList [1, 0]) :: Irrep SU2 1))
      (asSector1 (Irrep (fromList [0, 1]) :: Irrep SU2 1))
