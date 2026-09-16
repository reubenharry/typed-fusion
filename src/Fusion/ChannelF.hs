{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Channel F on irrep payloads from 'FusionData.fSymbol'.
--
-- For fixed @(a,b,c)@ and total @d@, left mids @e@ and right mids @f@ carry
-- vectors of length @dim(d)@ (SU(2): @d+1@). F acts as
-- @v'_f = Σ_e [F^{abc}_d]_{e f} v_e@ (and F⁻¹ \/ Fᵀ when @inv@).
module Fusion.ChannelF
  ( fmoveChannelsD
  , scaleIrrep
  ) where

import Control.Arrow.Constrained (arr)
import Data.Complex (Complex)
import Data.List (foldl')
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import qualified Data.Map.Strict as Map
import qualified Data.Vector.Storable as VS
import Data.VectorSpace (Scalar, VectorSpace ((*^)))
import Fusion.Data (FusionData (..), allowedLeftMids, allowedRightMids)
import GHC.TypeLits (KnownNat)
import Math.LinearMap.Category
  ( LSpace
  , pattern LinearFunction
  , type (+>)
  )
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.LinearMap.Category.Instances ()
import Math.OrphanInstances ()
import Numeric.LinearAlgebra.Static (C)
import Numeric.LinearAlgebra.Static.COrphans ()

-- | Scale an irrep payload (@C n +> C n@). Channel F is these scales on mids.
scaleIrrep
  :: forall n
   . (KnownNat n, LSpace (C n), Scalar (C n) ~ Complex Double)
  => Complex Double
  -> C n +> C n
scaleIrrep z = arr (LinearFunction (z *^))

scaleAdd
  :: Complex Double
  -> VS.Vector (Complex Double)
  -> VS.Vector (Complex Double)
  -> VS.Vector (Complex Double)
scaleAdd a u acc = VS.zipWith (\x y -> a * x + y) u acc

-- | Channel F from 'fSymbol' \/ mid lists. @dimOf d@ is the irrep payload length
-- (SU(2): @\\d -> d + 1@).
fmoveChannelsD
  :: forall lab t
   . ( FusionData lab t
     , Eq (TermLab t)
     , Ord (TermLab t)
     )
  => Proxy t
  -> (TermLab t -> Int)
  -> Bool
  -> TermLab t
  -> TermLab t
  -> TermLab t
  -> [(TermLab t, TermLab t, VS.Vector (Complex Double))]
  -> [(TermLab t, TermLab t, VS.Vector (Complex Double))]
fmoveChannelsD p dimOf inv a b c chans =
  let byD =
        Map.fromListWith
          (++)
          [(d, [(mid, v)]) | (d, mid, v) <- chans]
   in concatMap
        ( \(d, mids) ->
            let dim = dimOf d
                es = allowedLeftMids p a b c d
                fs = allowedRightMids p a b c d
                zero = VS.replicate dim 0
                get mid = fromMaybe zero (lookup mid mids)
             in if inv
                  then
                    [ ( d
                      , e
                      , foldl'
                          ( \acc (f, amp) -> scaleAdd amp (get f) acc
                          )
                          zero
                          (fSymbol p True a b c d e)
                      )
                    | e <- es
                    ]
                  else
                    let acc0 = Map.fromList [(f, zero) | f <- fs]
                        acc =
                          foldl'
                            ( \m e ->
                                foldl'
                                  ( \m' (f, amp) ->
                                      Map.insert
                                        f
                                        ( scaleAdd
                                            amp
                                            (get e)
                                            (Map.findWithDefault zero f m')
                                        )
                                        m'
                                  )
                                  m
                                  (fSymbol p False a b c d e)
                            )
                            acc0
                            es
                     in [(d, f, Map.findWithDefault zero f acc) | f <- fs]
        )
        (Map.toList byD)
