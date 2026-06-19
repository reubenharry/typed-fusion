
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
{-# LANGUAGE LambdaCase #-}
{- HLINT ignore "Parenthesize unary negation" -}
{- HLINT ignore "Move brackets to avoid $" -}
{- HLINT ignore "Redundant $" -}

module Experiments.SVD where

import Math.LinearMap.Category.Class
import Data.VectorSpace
import Control.Category.Constrained hiding (iso)
import Prelude hiding ((||), ($), id, (.))
import Math.LinearMap.Category (LinearFunction(..), HilbertSpace, Norm (Norm, applyNorm), euclideanNorm, (<$|), normSq, (|$|), (-+$>), (<.>^))
import Linear (V2 (V2), V3 (V3), E (..))
import Data.Coerce (Coercible)
import Math.LinearMap.Asserted
import Math.VectorSpace.Dual (Dual)
import Control.Arrow.Constrained (arr, Morphism (..), ($))
import qualified Control.Arrow.Constrained as C
import Math.LinearMap.Category (orthogonalComplementProj)
import qualified Debug.Trace
import Data.Functor.Identity (runIdentity)
import Math.VectorSpace.Initializable
import Math.LinearMap.Category.Instances
import Data.Number.NormedAlgebra (NormedAlgebra(RealPart))
import Data.Complex (Complex, realPart, Complex((:+)))

trace' a = Debug.Trace.trace (show a ++ " : debug")

a :: V3 Double -+> V3 Double
a = arr $ LinearMap $ V3 (V3 1.1 (-2.8) 3.2) (V3 (-1.2) 5.3 6.4) (V3 7.5 (-8.6) 9.7)

data SVDPendants v w = SVDPendants
          { domainSingularVector :: v
          , codomainSingularVector :: w
          , singularValue :: Scalar w
          }

svd :: (Show v, Show w, Scalar v ~ Double, Scalar w ~ Double, HilbertSpace v, HilbertSpace w, Monad m) => InitialVectors m v -> (v -+> w) -> Int -> m [SVDPendants v w]
svd initialVectors a dimA = do
        vecs <- sampleInitialVectors initialVectors
        let initialVector = head vecs
            vectors = tail vecs
        let steps = take dimA [svdStep v a | v <- vectors ]
            step = foldr (.) id steps
            initialPendant = SVDPendants
                (normalized initialVector)
                (normalized $ a $ initialVector)
                (magnitude (a $ initialVector))
        return (step [initialPendant])

svdC :: (Show v, Show w, Scalar v ~ Complex Double, Scalar w ~ Complex Double, HilbertSpace v, HilbertSpace w, Monad m) => InitialVectors m v -> (v -+> w) -> Int -> m [SVDPendants v w]
svdC initialVectors a dimA = do
        vecs <- sampleInitialVectors initialVectors
        let initialVector = head vecs
            vectors = tail vecs
        let steps = take dimA [svdStepC v a | v <- vectors ]
            step = foldr (.) id steps
            initialPendant = SVDPendants
                (normalized initialVector)
                (normalized $ a $ initialVector)
                (realSV $ realPart $ magnitude (a $ initialVector))
        return (step [initialPendant])


svdStep' :: forall v w . ( Show v, Show w, LinearSpace v, LinearSpace w
                   , Scalar v ~ Scalar w, RealFloat (Scalar v)
                   , Show v, Show w, Show (Scalar v), Num' (Scalar w), RealPart (Scalar w)
                    ~ Scalar w )
       => Norm v -> Norm w -> v -> (v -+> w)
            -> [SVDPendants v w] -> [SVDPendants v w]
svdStep' normV normW 𝐯 a svdPendants = trace' φ svdpendantsNew
-- trace' (assessOrthonormality $ map rhoV xBasis) $
 where xBasis = fmap domainSingularVector svdPendants
       yBasis = fmap codomainSingularVector svdPendants

       𝐯Orth = orthogonalComplementProj normV xBasis $ 𝐯

       -- A new vector in @v@, orthogonal to all the previously found
       -- singular-vector candidates.
       𝐱ₙ = 𝐯Orth ^/ (normV|$|𝐯Orth)
       𝐱ₙ' = normV<$|𝐱ₙ

       -- The corresponding result in @w@. This is /not/ orthogonal to the
       -- previous @w@-candidates!
       𝐲ₙ = a -+$> 𝐱ₙ
       𝐲ₙ' = normW<$|𝐲ₙ

       𝐲ₙCoefs = [𝐲ₙ'<.>^𝐲 | 𝐲 <- yBasis]

       -- Projection of @yn@ into the hyperplane spanned by @yBasis@
       𝐫 = sumV $ zipWith (*^) 𝐲ₙCoefs yBasis
       -- The preimage of this under @a@, using the fact that the previously
       -- found vectors diagonalize it on the subspaces.
       𝐪 = sumV $ zipWith3 (\μ p 𝐱 -> (μ / singularValue p)*^𝐱) 𝐲ₙCoefs svdPendants xBasis
       𝐪' = normV<$|𝐪
       𝑞 = sqrt $ 𝐪'<.>^𝐪
       𝐪hat = 𝐪 ^/ 𝑞

       φ = 1/2 * atan2 (2 * (𝐲ₙ'<.>^𝐫)) (normSq normW 𝐫 - 𝑞*(𝐲ₙ'<.>^𝐲ₙ))
    --    theta = - 0.5 * atan2 (-2 * (aqhat <.> yn)) (magnitudeSq aqhat - magnitudeSq yn)
       -- This is defined so the following becomes orthogonal:
       ρ𝐱ₙ = cos φ *^ 𝐱ₙ ^-^ (sin φ / 𝑞) *^ 𝐪
    --    ρ𝐪 = sin φ *^ 𝐱ₙ ^+^ (cos φ / 𝑞) *^ 𝐪

       -- Namely, the inner product is
       -- a(ρ𝐱ₙ)<.>a(ρ𝐱𝐪) = (cos φ^2 − sin φ^2)·(𝐲ₙ<.>𝐫/𝑞) + cos φ·sin φ·(‖𝐲ₙ‖² − 𝑟²/𝑞)
       --                 = (1 − 2·sin φ^2)·(𝐲ₙ<.>𝐫/𝑞) + sin (2φ)/2·(‖𝐲ₙ‖² − 𝑟²/𝑞)
       --                 = cos (2φ)·(𝐲ₙ<.>𝐫/𝑞) + sin (2φ)/2·(‖𝐲ₙ‖² − 𝑟²/𝑞)
       -- Set to 0:
       -- sin (2φ)·(𝑟²/𝑞 − ‖𝐲ₙ‖²) = cos (2φ)·2·(𝐲ₙ<.>𝐫/𝑞)
       -- tan (2φ) = 2·(𝐲ₙ<.>𝐫)/(𝑟² − 𝑞·‖𝐲ₙ‖²)


       -- Rotation operation, chosen in such a way that the rotated version
       -- becomes orthogonal to ρ𝐪, not only in @v@ but also in @w@, equivalent
       -- to the image under @a@.
       ρVW 𝐱 𝐲 = ( 𝐱 ^+^ ((cos φ - 1)*𝐱ₙOverlap) *^ 𝐱ₙ
                     ^-^ (sin φ*𝐱ₙOverlap / 𝑞) *^ 𝐪
                 , 𝐲 ^+^ ((cos φ - 1)*𝐱ₙOverlap) *^ 𝐲ₙ
                     ^-^ (sin φ*𝐱ₙOverlap / 𝑞) *^ 𝐫 )
        where 𝐱' = normV<$|𝐱
              𝐱ₙOverlap = 𝐱ₙ'<.>^𝐱

       rhoV v = v ^+^ (cos φ - 1) *^ (((𝐪' <.>^ v) *^ 𝐪hat) ^+^ ((𝐱ₙ' <.>^ v) *^ 𝐱ₙ)) ^+^ sin φ *^ (((𝐪' <.>^ v) *^ 𝐱ₙ) ^-^ ((𝐱ₙ' <.>^ v) *^ 𝐪hat))

       rotatedXBasis = map rhoV xBasis
       rotatedYBasisUnnormalized = map (a $) rotatedXBasis

       𝐲ₙOrth = cos φ *^ 𝐲ₙ ^-^ (sin φ / 𝑞) *^ 𝐫
       sn = normW |$| 𝐲ₙOrth
       𝐲ₙOrthnor = 𝐲ₙOrth ^/ sn

    --    (_, rotatedYBasisUnnormalized)
    --       = unzip $ zipWith ρVW xBasis yBasis
       sis = (normW|$|) <$> rotatedYBasisUnnormalized
       rotatedYBasis = zipWith (^/) rotatedYBasisUnnormalized sis

       svdpendantsNew = SVDPendants ρ𝐱ₙ 𝐲ₙOrthnor sn
                      : zipWith3 SVDPendants rotatedXBasis rotatedYBasis sis


exampleSvd :: [SVDPendants (V3 Double) (V3 Double)]
exampleSvd = runIdentity (svd (FixedInitialVectors [V3 1 0 0, V3 0 1 0, V3 0 0 1]) a 3)

-- svdStep v a svdPendants = trace' (innerProdsX, innerProdsY) svdpendantsNew
svdStep :: forall v w. (Show v, Show w, Scalar v ~ Double, Scalar w ~ Double, HilbertSpace v, HilbertSpace w) => v -> (v -+> w) -> [SVDPendants v w] ->
    [SVDPendants v w]
svdStep v a svdPendants = trace' (theta) $ svdpendantsNew
    where

    xBasis = fmap domainSingularVector svdPendants
    yBasis = fmap codomainSingularVector svdPendants
    singularVals = fmap singularValue svdPendants

    (xn, yn) = (normalized $ (orthogonalComplementProj euclideanNorm xBasis $ v), a $ xn)

    r = sumV [(yn <.> yi) *^ yi | yi <- yBasis]
    q = sumV [((r <.> yi) / si) *^ xi | (xi, yi, si) <- zip3 xBasis yBasis singularVals]
    qhat = normalized q

    rhoxn = negateV (sin theta *^ qhat) ^+^ cos theta *^ xn
    -- ρ𝐱ₙ = cos φ *^ 𝐱ₙ ^-^ (sin φ / 𝑞) *^ 𝐪
    rhoV v = v ^+^ (cos theta - 1) *^ (((qhat <.> v) *^ qhat) ^+^ ((xn <.> v) *^ xn)) ^+^ sin theta *^ (((qhat <.> v) *^ xn) ^-^ ((xn <.> v) *^ qhat))

    -- ρVW 𝐱 𝐲 = ( 𝐱 ^+^ ((cos φ - 1)*𝐱ₙOverlap) *^ 𝐱ₙ
    --                  ^-^ (sin φ*𝐱ₙOverlap / 𝑞) *^ 𝐪
    --              , 𝐲 ^+^ ((cos φ - 1)*𝐱ₙOverlap) *^ 𝐲ₙ
    --                  ^-^ (sin φ*𝐱ₙOverlap / 𝑞) *^ 𝐫 )
    --     where 𝐱' = normV<$|𝐱
    --           𝐱ₙOverlap = 𝐱ₙ'<.>^𝐱

    (ynTilde, sn, ynTildeHat) = (a $ rhoxn, magnitude ynTilde, normalized ynTilde)
    aqhat = r ^/ magnitude q
    theta = - 0.5 * atan2 (-2 * (aqhat <.> yn)) (magnitudeSq aqhat - magnitudeSq yn)

    (rotatedXBasis,
     rotatedYBasisUnnormalized,
     rotatedYBasis,
     sis) = (
        map rhoV xBasis,
        map  (a $) rotatedXBasis,
        normalized <$> rotatedYBasisUnnormalized,
        magnitude <$> rotatedYBasisUnnormalized)

    svdpendantsNew = SVDPendants rhoxn ynTildeHat sn : [SVDPendants x y s | (x,y,s) <- zip3 rotatedXBasis rotatedYBasis sis]

-- | Complex Hilbert-space SVD step (same algorithm as 'svdStep', with '(<.>^)').
svdStepC
  :: forall v w
   . ( Show v, Show w
     , Scalar v ~ Complex Double, Scalar w ~ Complex Double
     , HilbertSpace v, HilbertSpace w )
  => v -> (v -+> w) -> [SVDPendants v w] -> [SVDPendants v w]
svdStepC v a svdPendants = svdpendantsNew
  where
    normW = euclideanNorm @w
    xBasis = fmap domainSingularVector svdPendants
    yBasis = fmap codomainSingularVector svdPendants
    singularVals = fmap singularValue svdPendants

    xn = normalized $ (orthogonalComplementProj euclideanNorm xBasis) -+$> v
    yn = a -+$> xn

    r = sumV [(yn <.>^ yi) *^ yi | yi <- yBasis]
    q = sumV [((r <.>^ yi) / si) *^ xi | (xi, yi, si) <- zip3 xBasis yBasis singularVals]
    qhat = normalized q

    rhoxn = negateV (realSV (sin theta) *^ qhat) ^+^ realSV (cos theta) *^ xn
    rhoV v' =
      v' ^+^ realSV (cos theta - 1) *^ (((qhat <.>^ v') *^ qhat) ^+^ ((xn <.>^ v') *^ xn))
        ^+^ realSV (sin theta) *^ (((qhat <.>^ v') *^ xn) ^-^ ((xn <.>^ v') *^ qhat))

    ynTilde = a -+$> rhoxn
    sn = realSV (normW |$| ynTilde)
    ynTildeHat = normalized ynTilde
    aqhat = r ^/ magnitude q
    cross = realPart (aqhat <.>^ yn)
    theta = -0.5 * atan2 (-2 * cross) (normSq normW aqhat - normSq normW yn)

    rotatedXBasis = map rhoV xBasis
    rotatedYBasisUnnormalized = map (a -+$>) rotatedXBasis
    rotatedYBasis = normalized <$> rotatedYBasisUnnormalized
    sis = realSV . (normW |$|) <$> rotatedYBasisUnnormalized

    svdpendantsNew =
      SVDPendants rhoxn ynTildeHat sn
        : [SVDPendants x y s | (x, y, s) <- zip3 rotatedXBasis rotatedYBasis sis]

realSV :: Double -> Complex Double
realSV x = x :+ 0


testSVD :: IO ()
testSVD = do
    let assumeSingularVectors :: (InnerSpace v, RealFloat (Scalar v)) => (v-+>v) -> [v] -> [SVDPendants v v]
        assumeSingularVectors f xs = [SVDPendants x (fx ^/ s) s | x <- xs, let fx = f -+$> x; s = magnitude fx]

        euclSVDStep :: forall v w . ( LinearSpace v, LinearSpace w
                   , Scalar v ~ Scalar w, RealFloat (Scalar v)
                   , Show v, Show w, Show (Scalar v), Num' (Scalar w), RealPart (Scalar w)
                    ~ Scalar w, Coercible (DualVector v) v, Coercible (DualVector w) w )
           => v -> (v -+> w)
            -> [SVDPendants v w] -> [SVDPendants v w]
        euclSVDStep = svdStep' euclideanNorm euclideanNorm
        f = LinearFunction $ \(V3 x y z) -> V3 x (y+z) z
        preSVD :: [SVDPendants (V3 Double) (V3 Double)]
        preSVD = assumeSingularVectors f [V3 1 0 0, V3 0 1 0]
        postSVD' = euclSVDStep (V3 0 0 1) f preSVD
        postSVD = svdStep (V3 0 0 1) f preSVD
    print $ domainSingularVector <$> preSVD
    mapM_ print . assessOrthonormality $ codomainSingularVector <$> postSVD

    print("\n")

    mapM_ print . assessOrthonormality $ codomainSingularVector <$> postSVD'

assessOrthonormality xs = [[realToFrac (v<.>w) :: Float | w <- xs] | v <- xs]

foo  = let x1 = normalized $ V3 2.1 3.8 4.5
        --    x2 = normalized $ V2 4 5
           y1 = a $ x1
        --    y2 = a $ x2
  in svdStep (V3 1.2 (-3.5) 6.7) a [
    SVDPendants
     x1
     (normalized y1)
     (magnitude y1)
    --  SVDPendants
    --  x2
    --  y2
    --  (magnitude y2)
     ]

bar = svdStep (V3 4.7 (-0.8) 5.9) a foo

-- inv :: LinearMap Double (V3 Double) (V2 Double)
-- inv = xMat . pseudoInverse ((adjoint $ yMat) . arr a . xMat) . (adjoint $ yMat)
