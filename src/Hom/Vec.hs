{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

-- | Tiny helpers used by 'Examples.Symbolic'.
module Hom.Vec (vec) where

import Data.IndexedListLiterals (IndexedListLiterals)
import GHC.TypeLits (KnownNat)
import Numeric.LinearAlgebra.Static (C, Sized (..), fromList)
import qualified Data.Vector.Sized as VS

vec :: (Sized t c d, IndexedListLiterals a n t, KnownNat n, c ~ C n) => a -> c
vec a = (fromList . VS.toList . VS.fromTuple) a
