{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLists #-}

module TensorNetwork.MPS.FinSupp.FinSupp where
import TensorNetwork.MPS.General
import Data.VectorSpace.Free
import Data.Complex
import Math.LinearMap.Category
import Math.LinearMap.Asserted
import Data.VectorSpace.Free (FinSuppSeq(..))
import Data.VectorSpace.Free.FiniteSupportedSequence
import Linear.V1 (V1(..))


import Math.LinearMap.Category (type (-+>))
import Numeric.LinearAlgebra.Static hiding ((<.>))
import qualified Data.Vector.Unboxed as U
import Linear.V
import Control.Arrow.Constrained (EnhancedCat(arr))
import Prelude hiding (id, ($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($), arr)

mpsInfBond :: MPS (FinSuppSeq (Complex Double)) (C 2) 1
mpsInfBond = MPS 
  { mpsLeft = LinearMap [FinSuppSeq $ U.fromList [2,2]]
  , mpsBulk = toV $ V1 $ LinearMap []
  , mpsRight = LinearMap [2, 2,2,2]
  }

type InfBond = FinSuppSeq (Complex Double)

lowerInf :: InfBond -+> DualVector InfBond
lowerInf = lfun $ \x -> fromLinearForm $ (arr (LinearFunction (<.> x) ) :: InfBond +> Scalar InfBond )

raiseInf :: DualVector InfBond -+> InfBond
raiseInf = lfun $ \x -> [0]

infNorm :: FullNorm (FinSuppSeq (Complex Double))
infNorm = FullNorm (lowerInf) (raiseInf)

normInf = mpsInner infNorm hermitianNorm mpsInfBond mpsInfBond
