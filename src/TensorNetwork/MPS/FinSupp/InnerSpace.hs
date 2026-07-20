{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Sesquilinear 'InnerSpace' for complex 'FinSuppSeq' bonds.
--
-- The generic 'free-vector-spaces' instance is bilinear even for complex
-- entries; this orphan matches 'Numeric.LinearAlgebra.Static.COrphans' and
-- the DMRG convention (bra conjugation via 'dagger' / 'vectorConjugate', not
-- via a bilinear bond '<.>').
--
-- Also provides 'InnerTensorSpace' so @Bond ⊗ Bond@ can appear as the exact
-- product bond under MPO composition.
module TensorNetwork.MPS.FinSupp.InnerSpace where

import Prelude hiding (($))
import Control.Arrow.Constrained (($))
import Data.Complex (Complex, conjugate)
import Data.List (foldl')
import Data.VectorSpace (InnerSpace ((<.>)), AdditiveGroup (..))
import Data.VectorSpace.Free.FiniteSupportedSequence (FinSuppSeq (..))
import Math.LinearMap.Category
  ( type (⊗), Tensor (..), InnerTensorSpace (..)
  , (-+$>), pattern LinearFunction, bilinearFunction
  )
import Math.LinearMap.Category.Instances ()
import Math.OrphanInstances ()
import Numeric.LinearAlgebra.Static.COrphans ()
import qualified Data.Vector.Unboxed as U

type Field = Complex Double
type Bond = FinSuppSeq Field

finsuppInner :: U.Vector Field -> U.Vector Field -> Field
finsuppInner u v =
  go 0 0
  where
    lu = U.length u
    lv = U.length v
    go i acc
      | i >= lu && i >= lv = acc
      | otherwise =
          let ui = if i < lu then u U.! i else 0
              vi = if i < lv then v U.! i else 0
          in go (i + 1) (acc + conjugate ui * vi)

instance {-# OVERLAPPING #-} InnerSpace Bond where
  FinSuppSeq u <.> FinSuppSeq v = finsuppInner u v

-- | Frobenius-style lift over the list packing of @Bond ⊗ w@.
instance InnerTensorSpace Bond where
  liftTensorInner = LinearFunction $ \ip ->
    bilinearFunction $ \(Tensor ws) (Tensor xs) ->
      foldl'
        (^+^)
        zeroV
        (zipWith (\w x -> (ip -+$> w) -+$> x) ws xs)
