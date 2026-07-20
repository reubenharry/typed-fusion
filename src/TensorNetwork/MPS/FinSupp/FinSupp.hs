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
  , InfBond
  , mpsInfBond
  , infNorm
  , normInf
  , exampleIdCompose
  ) where

import TensorNetwork.MPS.General
import TensorNetwork.MPS.FinSupp.MPO
import TensorNetwork.MPS.FinSupp.InnerSpace ()
import Data.Complex
import Data.VectorSpace (InnerSpace ((<.>)), Scalar)
import Math.LinearMap.Category
  ( type (+>), type (-+>), DualVector, LinearMap (..)
  , pattern LinearFunction, lfun, fromLinearForm
  )
import Data.VectorSpace.Free.FiniteSupportedSequence (FinSuppSeq (..))
import Linear.V1 (V1 (..))
import Linear.V (toV)
import qualified Data.Vector.Unboxed as U
import Numeric.LinearAlgebra.Static (C)
import qualified Prelude as Prelude
import Prelude hiding (id, ($), (.))
import Control.Category.Constrained (id, (.))
import Control.Arrow.Constrained (($), arr)

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

-- | Smoke: @id . id@ stays the identity MPO on @C 2@ bulk length 1.
exampleIdCompose :: MPO Bond 1 (C 2) (C 2)
exampleIdCompose = id . id
