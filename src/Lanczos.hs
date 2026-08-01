{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{- HLINT ignore "Redundant $" -}
{- HLINT ignore "Use if" -}

-- | Matrix-free Lanczos for the lowest eigenpair of a Hermitian operator.
--
-- Orthogonalisation is the /three-term recurrence/ only (against @q_j@ and
-- @q_{j-1}@). That is enough in exact arithmetic for Hermitian @f@; we do
-- /not/ run full Gram–Schmidt against the whole Krylov basis (see
-- 'GroundState.gramSchmidt' / 'GroundState.buildKrylovBasis' for that path).
--
-- The metric is 'InnerSpace' @('<.>')@ (Hilbert–Schmidt on map centres). We
-- deliberately do /not/ use 'Norm'/'uncanonicallyToDual' or 'FullNorm'/'dagger'
-- for the centre: those need 'FiniteDimensional' Riesz wiring and disagree with
-- @('<.>')@ on @BulkSite@. Krylov coordinates @C m@ still use
-- 'FiniteDimensional' (typed @eigSH@ / 'asMap').
module Lanczos where

import Prelude hiding ((.), ($))
import Control.Arrow.Constrained (($), EnhancedCat (arr))
import Math.LinearMap.Category
  ( type (-+>)
  , LSpace, getLinearMap
  , FiniteDimensional (..), type (+>)
  , pattern LinearFunction
  )
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, Sized (fromList, extract))
import qualified Numeric.LinearAlgebra as H
import Data.VectorSpace
  ( AdditiveGroup ((^-^), zeroV), InnerSpace (..), Scalar
  , VectorSpace ((*^)), (^/)
  )
import Data.Complex (Complex ((:+)), realPart, magnitude)
import Data.Proxy (Proxy (..))
import GHC.TypeLits (KnownNat, Nat, SomeNat (..), natVal, someNatVal)
import System.Random (mkStdGen)
import qualified Test.QuickCheck as QC
import GroundState (randomHermitian)
import Random.Arbitrary ()
import Control.Category.Constrained.Prelude ((.), Category (..))
import Data.List (inits)
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE
import Data.Ord (comparing)
import Data.Maybe (mapMaybe)
import Data.Foldable (minimumBy)

-- | Breakdown / residual tolerance.
defaultLanczosTolerance :: Double
defaultLanczosTolerance = 1e-12

-- | Spaces on which Lanczos runs matrix-free (no 'FiniteDimensional' on @v@).
type Lanczos v =
  ( LSpace v
  , InnerSpace v
  , Scalar v ~ Complex Double
  , Floating (Scalar v)
  )

-- | Normalize @v@ under @('<.>')@; 'Nothing' if below 'defaultLanczosTolerance'.
normalizeVec
  :: (InnerSpace v, Scalar v ~ Complex Double, Floating (Scalar v))
  => v -> Maybe v
normalizeVec v =
  let nrm2 = realPart (v <.> v)
  in if nrm2 <= defaultLanczosTolerance
       then Nothing
       else Just (v ^/ (sqrt nrm2 :+ 0))

-- | One accepted Lanczos vector; @lanczosBetaNext@ is the next off-diagonal
-- (zero on breakdown).
data LanczosStep v = LanczosStep
  { lanczosQ :: v
  , lanczosBetaNext :: Double
  }

initNE :: NonEmpty a -> NonEmpty (NonEmpty a)
initNE steps =
  case mapMaybe NE.nonEmpty (drop 1 (inits (NE.toList steps))) of
    (p : ps) -> p :| ps
    [] -> steps :| []  -- unreachable for nonempty input

-- Forcing each cons cell does one matvec (three-term recurrence only). The
-- stream ends on breakdown (@β = 0@); until then it is as long as the consumer
-- demands. Subdiagonal entries of an @m@-step prefix are
-- @map lanczosBetaNext (init prefix)@; residual @β_{m+1}@ is
-- @lanczosBetaNext (last prefix)@.
--
-- Degenerate seed (norm below 'defaultLanczosTolerance') is an error: the first
-- Krylov vector is required for 'NE.unfoldr'.
lanczosTridiag
  :: Lanczos v
  => (v -+> v) -> v -> NonEmpty (LanczosStep v)
lanczosTridiag f seed =
  case normalizeVec seed of
    Nothing ->
      error "Lanczos.lanczosTridiag: degenerate seed (‖seed‖ ≈ 0)"
    Just q0 ->
      NE.unfoldr step (q0, zeroV, 0)
  where
    step (qj, qPrev, beta) =
      let w0 = (f $ qj) ^-^ ((beta :+ 0) *^ qPrev)
          alpha = realPart (qj <.> w0)
          w1 = w0 ^-^ ((alpha :+ 0) *^ qj)
          nrm2 = realPart (w1 <.> w1)
      in if nrm2 <= defaultLanczosTolerance
           then (LanczosStep qj 0, Nothing)
           else
             let beta' = sqrt nrm2
             in ( LanczosStep qj beta'
                , Just (w1 ^/ (beta' :+ 0), qj, beta')
                )

-- | Embed Krylov coordinates: @Q : w → v@ with columns the given ONB.
--
-- Precondition: @length qs == dim w@ (callers obtain @m@ via 'someNatVal').
-- 'FiniteDimensional' is only required on the Krylov coordinate space @w@.
asMap
  :: forall w v
   . (LSpace v, Scalar v ~ Scalar w, FiniteDimensional w)
  => NonEmpty v -> w +> v
asMap qs = fst (recomposeLinMap (entireBasis @w) (NE.toList qs))

-- | Change of basis into Krylov coordinates: @Q† : v → C m@.
--
-- @(Q† x)_i = ⟨qᵢ, x⟩@ under 'InnerSpace'. Precondition: @length qs == m@.
lanczosQDag
  :: forall m v
   . (KnownNat m, Lanczos v)
  => NonEmpty v -> v +> C m
lanczosQDag qs =
  arr $ LinearFunction $ \x ->
    fromList [ q <.> x | q <- NE.toList qs ]

-- | Residual estimate @‖f (Q y) − θ (Q y)‖ ≈ |β_{m+1} y_m|.
lanczosResidualEstimate :: forall m. KnownNat m => Double -> C m -> Double
lanczosResidualEstimate betaNext y =
  let i = fromIntegral (natVal (Proxy @m)) - 1
  in abs betaNext * magnitude (extract y `H.atIndex` i)

-- | True when the residual estimate is below @tol · (1 + |θ|)@.
lanczosConverged :: forall m. KnownNat m => Double -> Double -> C m -> Double -> Bool
lanczosConverged tol betaNext ys theta =
  lanczosResidualEstimate betaNext ys <= tol * (1 + abs theta)

--------------------------------------------------------------------------------
-- Rayleigh–Ritz: T = Q† f Q via typed maps
--------------------------------------------------------------------------------

data RitzPair (m :: Nat) v = RitzPair
  { ritzValue :: Double
  , ritzCoords :: C m
  , ritzVec :: v
  }

data RitzSpectrum (m :: Nat) v = RitzSpectrum
  { ritzPairs :: NonEmpty (RitzPair m v)
  , ritzBetaNext :: Double
  }

data SomeRitzSpectrum v where
  SomeRitzSpectrum :: KnownNat m => RitzSpectrum m v -> SomeRitzSpectrum v

ritzLowest :: RitzSpectrum m v -> RitzPair m v
ritzLowest = minimumBy (comparing ritzValue) . ritzPairs

solveSystem :: forall (m :: Nat) . KnownNat m
  => (C m -+> C m) -> NonEmpty (Double, C m)
solveSystem t =
  let (vals, vecs) = H.eigSH (H.sym (extract (getLinearMap $ arr t)))
      pairs =
        [ (vals `H.atIndex` i, fromList (H.toList col))
        | (i, col) <- zip [0 ..] (H.toColumns vecs)
        ]
  in case pairs of
       (p : ps) -> p :| ps
       [] ->
         let y = fromList (replicate (fromIntegral (natVal (Proxy @m))) 0)
         in (0, y) :| []

-- | @T = Q† ∘ f ∘ Q@ on Krylov coordinates.
basisChange
  :: forall m v
   . (KnownNat m, Lanczos v)
  => (v -+> v) -> (C m +> v) -> NonEmpty v -> C m -+> C m
basisChange f q qs = arr (lanczosQDag @m qs) . f . arr q

solveAtPrefix
  :: forall v
   . Lanczos v
  => (v -+> v) -> NonEmpty (LanczosStep v) -> SomeRitzSpectrum v
solveAtPrefix f prefix =
  case someNatVal (fromIntegral (NE.length prefix)) of
    Just (SomeNat (_ :: Proxy m)) ->
      let qs = fmap lanczosQ prefix
          q = asMap @(C m) qs
          spectrum = solveSystem (basisChange @m f q qs)
          pairs = (\(theta, y) -> RitzPair theta y (q $ y)) <$> spectrum
      in SomeRitzSpectrum (RitzSpectrum pairs (lanczosBetaNext (NE.last prefix)))
    Nothing -> error "unreachable: NE.length is nonnegative"

-- | Forms @T@ as @Q† f Q@ at each prefix, carries the full Ritz spectrum, and
-- selects the lowest only at the end.
lanczosLowestQ
  :: forall v
   . Lanczos v
  => (v -+> v) -> NonEmpty (LanczosStep v) -> Double -> (Double, v)
lanczosLowestQ f steps tol =
  case NE.break done $ solveAtPrefix f <$> initNE steps of
    (_, spectrum : _) -> getMinEig spectrum
    (pending, []) -> getMinEig (last pending)
  where
    getMinEig (SomeRitzSpectrum spectrum) =
      let RitzPair theta _ vec = ritzLowest spectrum
      in (theta, vec)
    done (SomeRitzSpectrum spectrum) =
      let RitzPair theta ys _ = ritzLowest spectrum
          betaNext = ritzBetaNext spectrum
      in betaNext <= defaultLanczosTolerance || lanczosConverged tol betaNext ys theta

-- | Lowest eigenpair of a Hermitian endomorphism via matrix-free Lanczos.
--
-- @maxDim@ caps the Krylov length (use the centre dimension, e.g. @χ·p·χ@ for
-- a bulk site). @seed@ should be the current centre tensor. Does not require
-- 'FiniteDimensional' on @v@.
groundStateLanczos
  :: forall v
   . Lanczos v
  => Int -> v -> (v +> v) -> (Double, v)
groundStateLanczos maxDim seed f =
  let f' = arr f
      -- 'NE.take' yields a list; @max 1 maxDim@ keeps it nonempty.
      steps = case NE.nonEmpty (NE.take (max 1 maxDim) (lanczosTridiag f' seed)) of
        Just s -> s
        Nothing -> error "Lanczos.groundStateLanczos: empty Krylov"
  in lanczosLowestQ f' steps defaultLanczosTolerance

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

prop_lanczosQDagEmbedIdC2 :: QC.Property
prop_lanczosQDagEmbedIdC2 =
  QC.forAll genNonZeroC2 $ \seed ->
  QC.forAll (QC.arbitrary :: QC.Gen Int) $ \g ->
  QC.forAll (QC.arbitrary :: QC.Gen (C 2)) $ \y ->
    let (h, _) = randomHermitian @(C 2) (mkStdGen g)
        steps = NE.take 2 (lanczosTridiag (arr h) seed)
    in case NE.nonEmpty steps of
         Just ne | NE.length ne == 2 ->
           let qs = fmap lanczosQ ne
               q = (arr $ asMap @(C 2) qs) :: C 2 -+> C 2
               qDag = (arr $ lanczosQDag @2 qs) :: C 2 -+> C 2
               y' = qDag $ (q $ y)
               diff = y' ^-^ y
               dist = sqrt (realPart (diff <.> diff))
           in QC.counterexample ("‖Q† Q y − y‖ = " ++ show dist) (dist < 1e-8)
         _ -> QC.counterexample "expected 2 Lanczos steps" False

genNonZeroC2 :: QC.Gen (C 2)
genNonZeroC2 =
  QC.arbitrary `QC.suchThat` \v -> realPart (v <.> v) > 1e-8

check :: IO ()
check = do
  seedVec <- QC.generate genNonZeroC2
  let (h, _) = randomHermitian @(C 2) (mkStdGen 0)
      h' = arr h
      krylovBasis = NE.take 2 $ lanczosTridiag h' seedVec
  case NE.nonEmpty krylovBasis of
    Nothing -> putStrLn "check: empty Krylov"
    Just ne -> do
      let qs = fmap lanczosQ ne
          q = asMap @(C 2) qs
          qDag = lanczosQDag @2 qs
          spectrum = solveSystem @2 (arr qDag . h' . arr q)
          (theta, y) = minimumBy (comparing fst) spectrum
          v = q $ y
          residual = (h' $ v) ^-^ ((theta :+ 0) *^ v)
          dist = sqrt (realPart (residual <.> residual))
      putStrLn $ "θ = " ++ show theta
      putStrLn $ "‖H (Q y) − θ (Q y)‖ = " ++ show dist

check2 :: IO ()
check2 = do
  seedVec <- QC.generate genNonZeroC2
  let (h, _) = randomHermitian @(C 2) (mkStdGen 0)
      h' = arr h
  case NE.nonEmpty (NE.take 2 (lanczosTridiag h' seedVec)) of
    Nothing -> putStrLn "check2: empty Krylov"
    Just steps -> print (lanczosLowestQ h' steps defaultLanczosTolerance)
