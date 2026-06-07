{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoStarIsType #-}

module Infinite where 

import qualified Data.Vector.Unboxed as U
import Data.VectorSpace.Free.FiniteSupportedSequence
import Data.Complex (Complex)
import Data.Basis (HasBasis(..))
import Math.LinearMap.Category (type (+>), LinearMap (..), (⊗), type (⊗), Num')
import Prelude hiding ((.), ($))
import Control.Arrow.Constrained (($))
import Linear.V2 (V2 (..))
import Numeric.LinearAlgebra.Static (R)
import Control.Category.Constrained.Prelude
import Numeric.LinearAlgebra.Static (C)


foo :: U.Vector (Complex Double)
foo = U.fromList [2,1, 3]

bar :: FinSuppSeq (Complex Double)
bar = FinSuppSeq foo 

linmap :: FinSuppSeq (Complex Double) +> FinSuppSeq ( Complex Double)
linmap = LinearMap [FinSuppSeq $ U.fromList [2,1, 3]]

-- comp :: FinSuppSeq (Complex Double) +> FinSuppSeq ( Complex Double)
-- comp = linmap . linmap

-- baz ::  Double
-- baz = decompose' bar 4

ban :: FinSuppSeq (Complex Double) +> V2 (Complex Double)
ban = LinearMap []

-- test :: V2 (Complex Double)
-- test = ban $ bar

-- instance Num' (Complex Double) where

data MPSClever vp = MPSClever {
    leftMPSClever :: C vp +> FinSuppSeq (Complex Double),
    center :: FinSuppSeq (Complex Double) +> C vp ⊗ FinSuppSeq (Complex Double),
    rightMPSClever :: FinSuppSeq (Complex Double) +> C vp
}

addClever :: MPSClever vp -> MPSClever vp -> MPSClever vp
addClever = undefined