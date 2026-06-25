{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

-- | Core types for growable-bond three-site MPS/MPO chains.
--
-- Bulk bonds are 'FinSuppSeq'. Left/right sites use the same transfer /
-- contraction *roles* as 'TensorNetwork.MPS.Fixed3', stored in the
-- linearmap-friendly shapes that support growable bonds:
--
--   * left  — @C p +> Bond@       (≅ @(C 1 ⊗ C p) +> Bond@ via the left unitor)
--   * bulk  — @Bond +> (C p ⊗ Bond)@
--   * right — @Bond +> C p@       (≅ @(Bond ⊗ C p) +> C 1@)
module TensorNetwork.MPS.FinSupp3.Internal
  ( Field
  , Bond
  , LeftSite (..)
  , BulkSite (..)
  , RightSite (..)
  , OpLeft (..)
  , OpBulk (..)
  , OpRight (..)
  , MPS (..)
  , MPO (..)
  , MPS3
  , MPO3
  , mps3
  , mpo3
  , withMPS3
  , withMPO3
  , Physical3
  , PhysicalDim3
  , vpDim
  , one1
  , unitBond
  , basisCvp
  ) where

import Data.Complex (Complex)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import Data.VectorSpace.Free.FiniteSupportedSequence (FinSuppSeq (..))
import qualified Data.Vector.Unboxed as U
import Math.LinearMap.Category (type (+>), type (⊗), LinearMap (..), Tensor (..))
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, Sized (..), fromList, create)
import GHC.TypeLits (KnownNat, Nat, type (*), natVal)
import qualified Numeric.LinearAlgebra as LA

type Field = Complex Double
type Bond = FinSuppSeq Field

type Physical3 p = C p ⊗ (C p ⊗ C p)
type PhysicalDim3 p = p * p * p

newtype LeftSite p = LeftSite { leftLin :: C p +> Bond }
newtype BulkSite p = BulkSite { bulkLin :: Bond +> (C p ⊗ Bond) }
newtype RightSite p = RightSite { rightLin :: Bond +> C p }

newtype OpLeft p = OpLeft { opLeftLin :: C p +> (Bond ⊗ C p) }
newtype OpBulk p = OpBulk { opBulkLin :: Bond +> (Bond ⊗ C p) }
newtype OpRight p = OpRight { opRightLin :: Bond +> C p }

data MPS (p :: Nat) = MPS
  { mpsLeft :: LeftSite p
  , mpsBulk :: BulkSite p
  , mpsRight :: RightSite p
  }

data MPO (p :: Nat) = MPO
  { mpoLeft :: OpLeft p
  , mpoBulk :: OpBulk p
  , mpoRight :: OpRight p
  }

type MPS3 p = MPS p
type MPO3 p = MPO p

mps3 :: LeftSite p -> BulkSite p -> RightSite p -> MPS3 p
mps3 = MPS

mpo3 :: OpLeft p -> OpBulk p -> OpRight p -> MPO3 p
mpo3 = MPO

withMPS3 :: MPS3 p -> (LeftSite p -> BulkSite p -> RightSite p -> a) -> a
withMPS3 (MPS l c r) k = k l c r

withMPO3 :: MPO3 p -> (OpLeft p -> OpBulk p -> OpRight p -> a) -> a
withMPO3 (MPO l c r) k = k l c r

vpDim :: forall p. KnownNat p => Int
vpDim = fromIntegral (natVal (Proxy @p))

one1 :: C 1
one1 = fromList [1]

unitBond :: Bond
unitBond = FinSuppSeq (U.fromList [1])

basisCvp :: forall p. KnownNat p => Int -> C p
basisCvp i =
  fromMaybe (error "basisCvp: create failed") $
    create (LA.fromList [ if j == i then 1 else 0 | j <- [0 .. vpDim @p - 1] ])
