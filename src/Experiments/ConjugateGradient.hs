
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{- HLINT ignore "Redundant $" -}

module Experiments.ConjugateGradient where

import Math.LinearMap.Category (LinearMap(..), type (⊗), (⊕), InnerSpace ((<.>)), (<.>^), (<$|), euclideanNorm, Norm (Norm), Tensor (Tensor), DualVector, TensorSpace (TensorProduct), VectorSpace ((*^), Scalar), LinearSpace, AdditiveGroup ((^+^), zeroV), (^-^))
import Linear (V2 (V2), V3 (V3), E (..))
import Data.Functor.Rep (tabulate, index)
import Control.Lens (Iso')
import Math.VectorSpace.DimensionAware
import Prelude hiding ((||), ($), id, (.))
import Math.LinearMap.Asserted
import Data.Complex
import Control.Arrow.Constrained (($), EnhancedCat (arr))
import Math.TensorNetwork (trace')


data ConjugateGradientState v = ConjugateGradientState {
    x :: v,
    r :: v,
    p :: v,
    alpha :: Scalar v,
    beta :: Scalar v
}

conjugateGradientStep :: (Fractional (Scalar v), TensorSpace v, InnerSpace v) => (v -+> v) -> ConjugateGradientState v -> ConjugateGradientState v
conjugateGradientStep f (ConjugateGradientState x r p alpha beta) = ConjugateGradientState x' r' p' alpha' beta' where
    alpha' = (r <.> r) / (p <.> (f $ p))
    x' = x ^+^ alpha' *^ p
    r' = r ^-^ alpha' *^ (f $ p)
    beta' = (r' <.> r') / (r <.> r)
    p' = r' ^+^ beta' *^ p


conjugateGradient :: (Ord (Scalar v), TensorSpace v, InnerSpace v, Fractional (Scalar v)) => Scalar v -> (v -+> v) -+> (v -+> v)
conjugateGradient tol = LinearFunction $ \f -> LinearFunction $ \b ->

    let initialState = ConjugateGradientState x0 b b 0 0
        x0 = zeroV
    in case dropWhile (\cg -> r cg <.> r cg > tol) (iterate (conjugateGradientStep f) initialState) of
            cg : _ -> x cg
            _ -> x0


main = do
    let f = (arr $ LinearMap $ (V2 (V2 0 2) (V2 2 0))) :: V2 (Double) -+> V2 (Double)
    let b = V2 1 2
    let tol = 1e-5
    let inverse = conjugateGradient tol
    let inv =  inverse $ f
    let solution = inv $ b
    print solution






    -- alphaNew = (r0 <.> r0) / (p0 <.> (f $ p0))
    -- xNew = x0 + alphaNew *^ p0
    -- rNew = r0 - alphaNew *^ (f $ p0)

    -- betaNew = (rNew <.> rNew) / (r0 <.> r0)
    -- pNew = rNew + betaNew *^ p0

    -- x = xNew
    -- r = rNew
    -- p = pNew

    -- while (euclideanNorm r > tol) do
    --     alphaNew = (r <.> r) / (p <.> (f $ p))
    --     x = x + alphaNew *^ p