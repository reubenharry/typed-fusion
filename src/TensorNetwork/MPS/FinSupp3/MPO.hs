{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

module TensorNetwork.MPS.FinSupp3.MPO
  ( identityMPO
  , composeMPO
  , mpoApplyMPS
  , mpoApplyFlat
  , mpoFromElement
  ) where

import Data.Maybe (fromMaybe)
import Math.LinearMap.Category (type (⊗), Tensor (..), LinearMap (..), AdditiveGroup (zeroV))
import Math.LinearMap.Category.Instances ()
import Numeric.LinearAlgebra.Static (C, Sized (..), create)
import GHC.TypeLits (KnownNat, type (*))
import qualified Data.Vector as V
import qualified Numeric.LinearAlgebra as LA
import TensorNetwork.MPS.FinSupp3.Internal
  ( Field, Bond, OpLeft (..), OpBulk (..), OpRight (..), MPO (..), MPS (..)
  , mpo3, basisCvp, vpDim, PhysicalDim3 )
import TensorNetwork.MPS.FinSupp3.Reference (mpoElement, mpoApplyFlatReference)
import TensorNetwork.MPS.FinSupp3.Physical (mpsFromFlat, mpsToFlat)

mpoApplyMPS
  :: forall p.
     ( KnownNat p, KnownNat (PhysicalDim3 p), KnownNat (p * p) )
  => MPO p -> MPS p -> MPS p
mpoApplyMPS mpo mps = mpsFromFlat (mpoApplyFlat mpo (mpsToFlat mps))

mpoApplyFlat
  :: forall p. (KnownNat p, KnownNat (PhysicalDim3 p)) => MPO p -> C (PhysicalDim3 p) -> C (PhysicalDim3 p)
mpoApplyFlat = mpoApplyFlatReference

composeMPO :: forall p. KnownNat p => MPO p -> MPO p -> MPO p
composeMPO h1 h2 = mpoFromElement composed
  where
    composed t1 t2 t3 s1 s2 s3 =
      sum
        [ mpoElement h1 t1 t2 t3 u1 u2 u3 * mpoElement h2 u1 u2 u3 s1 s2 s3
        | u1 <- [0 .. vpDim @p - 1]
        , u2 <- [0 .. vpDim @p - 1]
        , u3 <- [0 .. vpDim @p - 1]
        ]

identityMPO :: forall p. KnownNat p => MPO p
identityMPO =
  mpoFromElement $ \t1 t2 t3 s1 s2 s3 ->
    if t1 == s1 && t2 == s2 && t3 == s3 then 1 else 0

mpoFromElement
  :: forall p. KnownNat p
  => (Int -> Int -> Int -> Int -> Int -> Int -> Field)
  -> MPO p
mpoFromElement elem =
  let vp = vpDim @p
      terms =
        [ ((t1, t2, t3, s1, s2, s3), c)
        | t1 <- [0 .. vp - 1], t2 <- [0 .. vp - 1], t3 <- [0 .. vp - 1]
        , s1 <- [0 .. vp - 1], s2 <- [0 .. vp - 1], s3 <- [0 .. vp - 1]
        , let c = elem t1 t2 t3 s1 s2 s3
        , c /= 0
        ]
  in case terms of
       [] -> mpo3 (OpLeft zeroV) (OpBulk zeroV) (OpRight zeroV)
       _  ->
         mpo3
           (OpLeft (LinearMap (mpoLeftImgs @p terms)))
           (OpBulk (LinearMap (mpoCenterImgs @p terms)))
           (OpRight (LinearMap (mpoRightImgs @p terms)))

mpoLeftImgs
  :: forall p. KnownNat p => [((Int, Int, Int, Int, Int, Int), Field)] -> V.Vector (Bond ⊗ C p)
mpoLeftImgs terms =
  V.generate (vpDim @p) $ \t ->
    Tensor [ mpoLeftRow @p t r terms | r <- [0 .. length terms - 1] ]

mpoLeftRow
  :: forall p. KnownNat p => Int -> Int -> [((Int, Int, Int, Int, Int, Int), Field)] -> C p
mpoLeftRow t r terms =
  fromMaybe (error "mpoLeftRow") $
    create
      ( LA.fromList
          [ sum [ 1 | (i, ((t1, _, _, s1, _, _), _)) <- zip [0 ..] terms, t1 == t, i == r, s1 == s ]
          | s <- [0 .. vpDim @p - 1]
          ]
      )

mpoCenterImgs
  :: forall p. KnownNat p => [((Int, Int, Int, Int, Int, Int), Field)] -> [Bond ⊗ C p]
mpoCenterImgs terms =
  [ Tensor
      [ if r == i
          then fromMaybe (error "mpoCenterImgs") (create (coeffRow s2 1))
          else zeroCvp
      | r <- [0 .. length terms - 1]
    ]
  | (i, ((_, _, _, _, s2, _), _)) <- zip [0 ..] terms
  ]
  where
    coeffRow s2 c =
      LA.fromList [ if s == s2 then c else 0 | s <- [0 .. vpDim @p - 1] ]
    zeroCvp :: KnownNat p => C p
    zeroCvp = fromMaybe (error "zeroCvp") (create (LA.fromList (replicate (vpDim @p) 0)))

mpoRightImgs :: forall p. KnownNat p => [((Int, Int, Int, Int, Int, Int), Field)] -> [C p]
mpoRightImgs terms =
  [ fromMaybe (error "mpoRightImgs") (create (coeffRow s3 c))
  | ((_, _, _, _, _, s3), c) <- terms
  ]
  where
    coeffRow t3 c =
      LA.fromList [ if s == t3 then c else 0 | s <- [0 .. vpDim @p - 1] ]
