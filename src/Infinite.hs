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
import Math.LinearMap.Category (type (+>), LinearMap (..))
import Prelude hiding (($))
import Control.Arrow.Constrained (($))
import Linear.V2 (V2 (..))
import Numeric.LinearAlgebra.Static (R)


foo :: U.Vector ( Double)
foo = U.fromList [2,1, 3]

bar :: FinSuppSeq ( Double)
bar = FinSuppSeq foo 

baz ::  Double
baz = decompose' bar 4

ban :: FinSuppSeq ( Double) +> V2 ( Double)
ban = LinearMap []

test :: V2 ( Double)
test = ban $ bar

data MPSClever vp = MPSClever {
    leftMPSClever :: R vp +> FinSuppSeq Double,
    rightMPSClever :: R vp +> FinSuppSeq Double
}