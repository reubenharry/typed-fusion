{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module TensorNetwork.MPS.FinSupp.FinSupp where

import TensorNetwork.MPS.General
import TensorNetwork.MPS.FinSupp.MPO
import TensorNetwork.MPS.FinSupp.Bond (Bond)
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

-- | Blocked on a typed @Bond ⊗ C 2 ≅ flat@ iso for self-dual 'dagger'
-- (same issue as ROADMAP bra-pullback). The old 'tensorNorm' coerce path is
-- unsound because @DualVector (u ⊗ v) = u +> DualVector v@.
instance SiteDagger Bond (C 2) Bond where
  siteDagger = undefined

mpsInfBond :: MPS Bond (C 2) 1
mpsInfBond = MPS
  { _mpsLeft = LinearMap [FinSuppSeq Prelude.$ U.fromList [2, 2]]
  , _mpsBulk = toV Prelude.$ V1 Prelude.$ LinearMap []
  , _mpsRight = LinearMap [2, 2, 2, 2]
  }


lowerInf :: Bond -+> DualVector Bond
lowerInf = lfun Prelude.$ \x -> fromLinearForm $ (arr (LinearFunction (<.> x)) :: Bond +> Scalar Bond)

raiseInf :: DualVector Bond -+> Bond
raiseInf = lfun Prelude.$ \_ -> [0]

infNorm :: FullNorm Bond
infNorm = FullNorm lowerInf raiseInf

normInf :: Complex Double
normInf = mpsInner infNorm hermitianNorm mpsInfBond mpsInfBond

-- | Smoke: @id . id@ stays the identity MPO on @C 2@ bulk length 1.
exampleIdCompose :: MPO Bond 1 (C 2) (C 2)
exampleIdCompose = id . id
