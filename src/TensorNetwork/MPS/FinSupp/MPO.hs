{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

module TensorNetwork.MPS.FinSupp.MPO where

import Data.Maybe (fromMaybe)
import Math.LinearMap.Category (type (⊗), Tensor (..), LinearMap (..), AdditiveGroup (zeroV))
import Math.LinearMap.Category.Instances ()
import Numeric.LinearAlgebra.Static (C, Sized (..), create)
import GHC.TypeLits (KnownNat, type (*))
import qualified Data.Vector as V
import qualified Numeric.LinearAlgebra as LA
import TensorNetwork.MPS.General (MPS (..), MPO (..))
