{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PatternSynonyms #-}

module TensorNetwork.MPS.FinSupp.FinSupp
  ( -- * Re-exports
    module TensorNetwork.MPS.FinSupp.MPO
  , Bond
  , InfBond
  , mpsInfBond
  , infNorm
  , normInf
  ) where

import TensorNetwork.MPS.General
import TensorNetwork.MPS.FinSupp.MPO
import TensorNetwork.MPS.FinSupp.Bond (Bond)
import TensorNetwork.MPS.FinSupp.InnerSpace ()
import Data.Complex
import Data.VectorSpace (InnerSpace ((<.>)), Scalar)
import Math.LinearMap.Category
import Math.LinearMap.Asserted
import Data.VectorSpace.Free.FiniteSupportedSequence (FinSuppSeq (..))
import Linear.V1 (V1 (..))
import Linear.V (toV)
import qualified Data.Vector.Unboxed as U
import Numeric.LinearAlgebra.Static hiding ((<.>))
import qualified Prelude as Prelude
import Prelude hiding (id, ($), (.))
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($), arr)
import Math.LinearMap.Category (type (-+>), pattern LinearFunction, lfun)

mpsInfBond :: MPS Bond (C 2) 1
mpsInfBond = MPS
  { mpsLeft = LinearMap [FinSuppSeq Prelude.$ U.fromList [2, 2]]
  , mpsBulk = toV Prelude.$ V1 Prelude.$ LinearMap []
  , mpsRight = LinearMap [2, 2, 2, 2]
  }

type InfBond = Bond

lowerInf :: InfBond -+> DualVector InfBond
lowerInf = lfun Prelude.$ \x -> fromLinearForm $ (arr (LinearFunction (<.> x)) :: InfBond +> Scalar InfBond)

raiseInf :: DualVector InfBond -+> InfBond
raiseInf = lfun Prelude.$ \_ -> [0]

infNorm :: FullNorm Bond
infNorm = FullNorm lowerInf raiseInf

normInf :: Complex Double
normInf = mpsInner infNorm hermitianNorm mpsInfBond mpsInfBond
