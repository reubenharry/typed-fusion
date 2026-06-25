{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

module TensorNetwork.MPS.FinSupp3.Reference
  ( applyLeftSite
  , applyBulkSite
  , applyRightSite
  , applyOpLeft
  , applyOpBulk
  , applyOpRight
  , amplitude
  , mpoElement
  , flatIndex3
  , mpsToFlatReference
  , mpoApplyFlatReference
  , cvpCoeff
  ) where

import Prelude hiding (($))
import Control.Arrow.Constrained (($))
import Math.LinearMap.Category (type (⊗), Tensor (..))
import Math.LinearMap.Category.Instances ()
import Numeric.LinearAlgebra.Static (C, Sized (unwrap, fromList, extract))
import GHC.TypeLits (KnownNat)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Storable as VS
import TensorNetwork.MPS.FinSupp3.Internal
  ( Bond (..), Field, LeftSite (..), BulkSite (..), RightSite (..)
  , OpLeft (..), OpBulk (..), OpRight (..), MPS (..), MPO (..)
  , withMPS3, withMPO3, basisCvp, vpDim, PhysicalDim3 )
import TensorNetwork.MPS.FinSupp3.Bond (applyBondMap)

cvpCoeff :: KnownNat p => C p -> Int -> Field
cvpCoeff v s = (VS.toList (unwrap (extract v))) !! s

codomainBondRows :: KnownNat p => Bond ⊗ C p -> V.Vector (C p)
codomainBondRows (Tensor rows) = rows

applyLeftSite :: forall p. KnownNat p => LeftSite p -> Int -> Bond
applyLeftSite (LeftSite l) s = l $ basisCvp @p s

applyBulkSite :: KnownNat p => BulkSite p -> Bond -> Int -> Bond
applyBulkSite (BulkSite c) bond s =
  let Tensor rows = applyBondMap bond (bulkLin c)
  in rows V.! s

applyRightSite :: KnownNat p => RightSite p -> Bond -> Int -> Field
applyRightSite (RightSite r) bond s = cvpCoeff (applyBondMap bond (rightLin r)) s

applyOpLeft :: forall p. KnownNat p => OpLeft p -> Int -> Int -> Bond
applyOpLeft (OpLeft op) t s =
  let rows = codomainBondRows (opLeftLin op $ basisCvp @p t)
  in FinSuppSeq $
       U.fromList [ cvpCoeff (rows V.! r) s | r <- [0 .. V.length rows - 1] ]

applyOpBulk :: KnownNat p => OpBulk p -> Bond -> Int -> Int -> Bond
applyOpBulk (OpBulk op) wl t s =
  let rows = codomainBondRows (applyBondMap wl (opBulkLin op))
  in FinSuppSeq $
       U.fromList [ cvpCoeff (rows V.! r) s | r <- [0 .. V.length rows - 1] ]

applyOpRight :: KnownNat p => OpRight p -> Bond -> Int -> Int -> Field
applyOpRight (OpRight op) wl _ s = cvpCoeff (applyBondMap wl (opRightLin op)) s

amplitude :: KnownNat p => MPS p -> Int -> Int -> Int -> Field
amplitude mps s1 s2 s3 =
  withMPS3 mps $ \l c r ->
    let b1 = applyLeftSite l s1
        b2 = applyBulkSite c b1 s2
    in applyRightSite r b2 s3

flatIndex3 :: Int -> Int -> Int -> Int -> Int
flatIndex3 p s1 s2 s3 = s1 + p * s2 + p * p * s3

mpsToFlatReference
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => MPS p -> C (PhysicalDim3 p)
mpsToFlatReference mps =
  fromList
    [ amplitude mps s1 s2 s3
    | s3 <- [0 .. vp - 1], s2 <- [0 .. vp - 1], s1 <- [0 .. vp - 1] ]
  where vp = vpDim @p

mpoElement
  :: KnownNat p => MPO p -> Int -> Int -> Int -> Int -> Int -> Int -> Field
mpoElement mpo t1 t2 t3 s1 s2 s3 =
  withMPO3 mpo $ \l c r ->
    let w1 = applyOpLeft l t1 s1
        w2 = applyOpBulk c w1 t2 s2
    in applyOpRight r w2 t3 s3

flatCoeff :: forall p. KnownNat p => C (PhysicalDim3 p) -> Int -> Int -> Int -> Field
flatCoeff v s1 s2 s3 = cvpCoeff v (flatIndex3 (vpDim @p) s1 s2 s3)

mpoApplyFlatReference
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => MPO p -> C (PhysicalDim3 p) -> C (PhysicalDim3 p)
mpoApplyFlatReference mpo v =
  fromList
    [ sum
        [ mpoElement mpo t1 t2 t3 s1 s2 s3 * flatCoeff v s1 s2 s3
        | t1 <- [0 .. vp - 1], t2 <- [0 .. vp - 1], t3 <- [0 .. vp - 1]
        ]
    | s3 <- [0 .. vp - 1], s2 <- [0 .. vp - 1], s1 <- [0 .. vp - 1] ]
  where vp = vpDim @p
