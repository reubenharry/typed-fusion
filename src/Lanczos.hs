{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{- HLINT ignore "Redundant $" -}
{- HLINT ignore "Use if" -}

-- | Matrix-free Lanczos for the lowest eigenpair of a Hermitian operator.
--
-- Orthogonalisation is the /three-term recurrence/ only (against @q_j@ and
-- @q_{j-1}@). That is enough in exact arithmetic for Hermitian @f@; we do
-- /not/ run full Gram–Schmidt against the whole Krylov basis (see
-- 'GroundState.gramSchmidt' / 'GroundState.buildKrylovBasis' for that path).
--
-- Rayleigh–Ritz uses @Q† = dagger nv (hermitianNorm @(C m)) Q@, so map-space
-- centres need only @DualVector (DualVector v) ~ v@ (not @DualVector v ~ v@).
module Lanczos where

import Prelude hiding ((.), ($))
import Control.Arrow.Constrained (($), EnhancedCat (arr))
import Math.LinearMap.Category
  ( type (-+>)
  , Norm (..), LSpace, euclideanNorm
  , getLinearMap
  , (<$|), (<.>^), FiniteDimensional (..), type (+>), DualVector, LinearMap, Num'
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
import Data.List (unfoldr, inits)
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE
import Data.Ord (comparing)
import Data.Maybe (mapMaybe)
import Data.Foldable (minimumBy)
import TensorNetwork.MPS.General (FullNorm (..), dagger, hermitianNorm)
import Math.LinearMap.Category.Class

-- | Breakdown / residual tolerance.
defaultLanczosTolerance :: Double
defaultLanczosTolerance = 1e-12

normInner :: LSpace v => Norm v -> v -> v -> Scalar v
normInner me u w = (me <$| u) <.>^ w

-- | Project a 'FullNorm' to the 'Norm' used by 'lanczosTridiag'.
normFromFull :: FullNorm v -> Norm v
normFromFull (FullNorm lo _) = Norm lo

-- | Normalize @v@ under @me@; 'Nothing' if below 'defaultLanczosTolerance'.
normalizeVec
  :: (LSpace v, Scalar v ~ Complex Double, Floating (Scalar v))
  => Norm v -> v -> Maybe v
normalizeVec me v =
  let nrm2 = realPart (normInner me v v)
  in if nrm2 <= defaultLanczosTolerance
       then Nothing
       else Just (v ^/ (sqrt nrm2 :+ 0))

-- | One accepted Lanczos vector: Rayleigh @α_j@ and next off-diagonal @β_{j+1}@
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
-- list ends on breakdown (@β = 0@); until then it is as long as the consumer
-- demands. Subdiagonal entries of an @m@-step prefix are
-- @map lanczosBetaNext (init prefix)@; residual @β_{m+1}@ is
-- @lanczosBetaNext (last prefix)@.
lanczosTridiag :: ( LSpace v, Scalar v ~ Complex Double, Floating (Scalar v) )
  => Norm v -> (v -+> v) -> v -> [LanczosStep v]
lanczosTridiag me f seed =
  -- State is @Maybe (qⱼ, qⱼ₋₁, βⱼ)@; @Nothing@ ends the stream (after a
  -- breakdown step has already been yielded).
  unfoldr (>>= step) ((, zeroV, 0) <$> normalizeVec me seed)
  where
    step (qj, qPrev, beta) =
      let -- Three-term: w ← f qⱼ − βⱼ qⱼ₋₁ − αⱼ qⱼ
          w0 = (f $ qj) ^-^ ((beta :+ 0) *^ qPrev)
          alpha = realPart (normInner me qj w0)
          w1 = w0 ^-^ ((alpha :+ 0) *^ qj)
          nrm2 = realPart (normInner me w1 w1)
      in Just if nrm2 <= defaultLanczosTolerance
           then (LanczosStep qj 0, Nothing)
           else
             let beta' = sqrt nrm2
             in ( LanczosStep qj beta'
                  , Just (w1 ^/ (beta' :+ 0), qj, beta')
                  )

-- | Embed Krylov coordinates: @Q : C m → v@ with columns the given ONB.
--
-- Precondition: @length qs == m@ (callers obtain @m@ via 'someNatVal').
-- Named @asMap@ to avoid clashing with the 'lanczosQ' field.
asMap :: forall w v . (LSpace v, Scalar v ~ Scalar w, FiniteDimensional w)
  => NonEmpty v -> w +> v
asMap qs = fst (recomposeLinMap (entireBasis @w) (NE.toList qs))

-- | Change of basis into Krylov coordinates: @Q† : v → C m@.
--
-- @Q† = dagger nv (hermitianNorm @(C m)) Q@. Precondition: @length qs == m@.
-- With 'asMap', Rayleigh–Ritz is @Q† ∘ f ∘ Q@.
lanczosQDag
  :: forall m v
   . ( KnownNat m
     , LSpace v
     , LSpace (DualVector v)
     , Scalar v ~ Complex Double
     , Scalar (DualVector v) ~ Complex Double
     , DualVector (DualVector v) ~ v
     )
  => FullNorm v -> NonEmpty v -> v +> C m
lanczosQDag nv qs =
  dagger nv (hermitianNorm @(C m)) (asMap @(C m) qs)

-- | Residual estimate @‖f (Q y) − θ (Q y)‖ ≈ |β_{m+1} y_m|.
--
-- Precondition: @m ≥ 1@ (as for any Krylov prefix from 'NonEmpty').
lanczosResidualEstimate :: forall m. KnownNat m => Double -> C m -> Double
lanczosResidualEstimate betaNext y =
  let i = fromIntegral (natVal (Proxy @m)) - 1
  in abs betaNext * magnitude (extract y `H.atIndex` i)

-- | True when the residual estimate is below @tol · (1 + |θ|)@.
lanczosConverged :: forall m. KnownNat m => Double -> Double -> C m -> Double -> Bool
lanczosConverged tol betaNext ys theta = lanczosResidualEstimate betaNext ys <= tol * (1 + abs theta)

--------------------------------------------------------------------------------
-- Alternative path: T = Q† f Q via typed maps, stream over growing prefixes
--------------------------------------------------------------------------------

-- | One eigenpair of a Rayleigh–Ritz @T@ at Krylov length @m@.
data RitzPair (m :: Nat) v = RitzPair
  { ritzValue :: Double
  , ritzCoords :: C m
  , ritzVec :: v
  }

-- | Full spectrum at a fixed Krylov length @m@, plus residual @β_{m+1}@.
data RitzSpectrum (m :: Nat) v = RitzSpectrum
  { ritzPairs :: NonEmpty (RitzPair m v)
  , ritzBetaNext :: Double
  }

-- | Spectrum at some Krylov length (hides @m@ so the stream can grow).
data SomeRitzSpectrum v where
  SomeRitzSpectrum :: KnownNat m => RitzSpectrum m v -> SomeRitzSpectrum v

ritzLowest :: RitzSpectrum m v -> RitzPair m v
ritzLowest = minimumBy (comparing ritzValue) . ritzPairs

-- | Full eigen-decomposition of a typed @T : C m → C m@.
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
         -- unreachable for @m ≥ 1@: @eigSH@ returns @m@ eigenpairs
         let y = fromList (replicate (fromIntegral (natVal (Proxy @m))) 0)
         in (0, y) :| []

-- basisChange :: (Scalar c ~ Scalar b, Scalar (DualVector c) ~ Scalar b,  Scalar (DualVector b) ~ Scalar b, DualVector (DualVector b) ~ b,  Object k b,  Object k c,  EnhancedCat k (LinearMap (Scalar b)),  Num' (Scalar b),  LinearSpace b,  LinearSpace c,  LinearSpace (DualVector c),  LinearSpace (DualVector b)) => FullNorm b -> k b b -> LinearMap (Scalar b) c b -> k c c
basisChange nb nc f q = arr (dagger nb nc q) . f . arr q

-- | Build @T = Q† f Q@ at the prefix length, return the full lifted spectrum.
solveAtPrefix
  :: forall v
   . Lanczos v
  => FullNorm v -> (v -+> v) -> NonEmpty (LanczosStep v) -> SomeRitzSpectrum v
solveAtPrefix nv f prefix =
  case someNatVal (fromIntegral (NE.length prefix)) of
    Just (SomeNat (_ :: Proxy m)) ->
      let qs = fmap lanczosQ prefix
          q = asMap @(C m) qs
          spectrum = solveSystem (basisChange nv (hermitianNorm @(C m)) f q)
          pairs = (\(theta, y) -> RitzPair theta y (q $ y)) <$> spectrum
      in SomeRitzSpectrum (RitzSpectrum pairs (lanczosBetaNext (NE.last prefix)))
    Nothing -> error "unreachable: NE.length is nonnegative"

type Lanczos v = ( LSpace v
     , LSpace (DualVector v)
     , Scalar v ~ Complex Double
     , Scalar (DualVector v) ~ Complex Double
     , Floating (Scalar v)
     , DualVector (DualVector v) ~ v
     )

-- | Forms @T@ as @Q† f Q@ at each prefix, carries the full Ritz spectrum, and
-- selects the lowest only at the end.
lanczosLowestQ
  :: forall v
   . Lanczos v
  => FullNorm v -> (v -+> v) -> NonEmpty (LanczosStep v) -> Double -> (Double, v)
lanczosLowestQ nv f steps tol =
  case NE.break done $ solveAtPrefix nv f <$> initNE steps of
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

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

-- | @Q† ∘ Q ≈ id@ on Krylov coordinates for a full-dim Lanczos prefix.
prop_lanczosQDagEmbedIdC2 :: QC.Property
prop_lanczosQDagEmbedIdC2 =
  QC.forAll genNonZeroC2 $ \seed ->
  QC.forAll (QC.arbitrary :: QC.Gen Int) $ \g ->
  QC.forAll (QC.arbitrary :: QC.Gen (C 2)) $ \y ->
    let (h, _) = randomHermitian @(C 2) (mkStdGen g)
        nv = hermitianNorm @(C 2)
        steps = take 2 (lanczosTridiag euclideanNorm (arr h) seed)
    in case NE.nonEmpty steps of
         Just ne | NE.length ne == 2 ->
           let qs = fmap lanczosQ ne
               q = (arr $ asMap @(C 2) qs) :: C 2 -+> C 2
               qDag = (arr $ lanczosQDag @2 nv qs) :: C 2 -+> C 2
               y' = qDag $ (q $ y)
               diff = y' ^-^ y
               dist = sqrt (realPart (diff <.> diff))
           in QC.counterexample ("‖Q† Q y − y‖ = " ++ show dist) (dist < 1e-8)
         _ -> QC.counterexample "expected 2 Lanczos steps" False

genNonZeroC2 :: QC.Gen (C 2)
genNonZeroC2 =
  QC.arbitrary `QC.suchThat` \v -> realPart (v <.> v) > 1e-8

-- | Smoke: full-dim Lanczos @T = Q† H Q@, lowest of the full spectrum lifted by
-- @Q@ recovers (approx.) the lowest eigenvector of @H@. Exact when @m = dim@.
check :: IO ()
check = do
  seedVec <- QC.generate genNonZeroC2
  let (h, _) = randomHermitian @(C 2) (mkStdGen 0)
      h' = arr h
      nv = hermitianNorm @(C 2)
      krylovBasis = take 2 $ lanczosTridiag euclideanNorm h' seedVec
  case NE.nonEmpty krylovBasis of
    Nothing -> putStrLn "check: empty Krylov"
    Just ne -> do
      let qs = fmap lanczosQ ne
          q = asMap @(C 2) qs
          qDag = lanczosQDag @2 nv qs
          spectrum = solveSystem @2 (arr qDag . h' . arr q)
          (theta, y) = minimumBy (comparing fst) spectrum
          v = q $ y
          residual = (h' $ v) ^-^ ((theta :+ 0) *^ v)
          dist = sqrt (realPart (residual <.> residual))
      putStrLn $ "θ = " ++ show theta
      putStrLn $ "‖H (Q y) - θ (Q y)‖ = " ++ show dist

check2 :: IO ()
check2 = do
  seedVec <- QC.generate genNonZeroC2
  let (h, _) = randomHermitian @(C 2) (mkStdGen 0)
      h' = arr h
      nv = hermitianNorm @(C 2)
  case NE.nonEmpty (take 2 (lanczosTridiag euclideanNorm h' seedVec)) of
    Nothing -> putStrLn "check2: empty Krylov"
    Just steps -> print (lanczosLowestQ nv h' steps defaultLanczosTolerance)
