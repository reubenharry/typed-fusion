{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

-- | Ground-state solver for a local effective Hamiltonian (ROADMAP §4b).
--
-- * 'groundState' / 'spectrum' use dense @hmatrix@ 'eigSH' on 'toDenseMatrix'
--   (interim default for map-space centres until map-space Krylov is validated).
-- * 'groundStateEigen' / 'spectrumEigen' use linearmap's 'constructEigenSystem'
--   with a supplied 'Norm' on @v -+> v@ endomorphisms, and require
--   'FiniteDimensional'.
-- * 'groundStateKrylov' / 'groundStateKrylovMap' also use 'constructEigenSystem',
--   but only require 'LSpace' + 'InnerSpace' (not 'FiniteDimensional'), so they
--   can target map-space centres once the linearmap instances are in place.
--   Pass Krylov seed vectors explicitly when no canonical basis exists.
--   Note: @FinSuppSeq@ bond centres still need an 'InnerTensorSpace' instance
--   for 'Sequence' (the dual of 'FinSuppSeq') in linearmap before Krylov
--   can run on @FinSuppSeq +> …@ sites.
--
-- 'hilbertSchmidtNorm' and 'toDenseMatrix' are exported for tests and the
-- eventual full map-space migration.
module GroundState
  ( toDenseMatrix
  , hilbertSchmidtNorm
  , defaultEigenTolerance
  , groundStateDense
  , spectrumDense
  , groundStateEigen
  , spectrumEigen
  , groundStateKrylov
  , groundStateKrylovMap
  , groundState
  , spectrum
  , smokeRandomEffectiveHamiltonian
  ) where

import Prelude hiding (($))
import Control.Arrow.Constrained (($), EnhancedCat (arr))
import Math.LinearMap.Category
  ( type (+>), type (-+>), type (⊗)
  , FiniteDimensional (..), SubBasis
  , eigen, Norm (..), LSpace
  , constructEigenSystem, finishEigenSystem, Eigenvector (..)
  , recomposeLinMap, recomposeSB, entireBasis )
import Data.VectorSpace (InnerSpace (..), Scalar, VectorSpace ((*^)), sumV)
import Data.Number.NormedAlgebra (NormedAlgebra (RealPart))
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C)
import qualified Numeric.LinearAlgebra as H
import Data.Complex (Complex ((:+)), realPart, conjugate)
import Data.List (sort, minimumBy)
import Data.Ord (comparing)
import Numeric.IEEE (IEEE)
import System.Random (StdGen, newStdGen, randomR, split)
import Control.Exception (SomeException, evaluate, try)

-- | The standard basis vectors of @v@ (linearmap-category's canonical finite
-- basis). For @C n@ and tensor/map spaces over it these have real 0/1 entries,
-- which is what makes the matrix read-off below convention-free.
basisOf :: forall v. FiniteDimensional v => [v]
basisOf = enumerateSubBasis (entireBasis :: SubBasis v)

-- | Hilbert–Schmidt norm via 'uncanonicallyToDual' (for map-space Krylov).
hilbertSchmidtNorm :: FiniteDimensional v => Norm v
hilbertSchmidtNorm = Norm uncanonicallyToDual

-- | Target eigen-residual tolerance passed to 'constructEigenSystem'.
defaultEigenTolerance :: Double
defaultEigenTolerance = 1e-12

-- | Materialise an endomorphism as a dense matrix in the canonical basis
-- (@e_i \<.\> f e_j@). Regression oracle and dense-solver input.
toDenseMatrix
  :: forall v. (FiniteDimensional v, InnerSpace v, Scalar v ~ Complex Double)
  => (v +> v) -> H.Matrix (Complex Double)
toDenseMatrix f =
  let es   = basisOf @v
      cols = [ f $ e | e <- es ]
  in H.fromLists [ [ ei <.> colj | colj <- cols ] | ei <- es ]

-- | Dense @hmatrix@ route (interim default).
groundStateDense
  :: forall v. (FiniteDimensional v, InnerSpace v, Scalar v ~ Complex Double)
  => (v +> v) -> (Double, v)
groundStateDense f =
  let (vals, vecs) = H.eigSH (H.sym (toDenseMatrix f))
      idx          = H.minIndex vals
      eval         = vals `H.atIndex` idx
  in case drop idx (H.toColumns vecs) of
       (evec : _) ->
         let coords   = H.toList evec
             (vec, _) = recomposeSB (entireBasis :: SubBasis v) coords
         in (eval, vec)
       [] -> error "GroundState.groundStateDense: empty eigenvector set"

spectrumDense
  :: ( FiniteDimensional v, InnerSpace v, Scalar v ~ Complex Double )
  => (v +> v) -> [Double]
spectrumDense f =
  let (vals, _) = H.eigSH (H.sym (toDenseMatrix f))
  in reverse (H.toList vals)

-- | Grow a Krylov eigenbasis until the canonical basis dimension is reached.
completeEigenSystem
  :: forall v
   . ( FiniteDimensional v, LSpace v, Scalar v ~ Complex Double
     , RealFloat (RealPart (Scalar v)) )
  => Norm v -> RealPart (Scalar v) -> (v -+> v) -> [v] -> [Eigenvector v]
completeEigenSystem norm tol f seeds =
  let dim = length (basisOf @v)
      stream = constructEigenSystem norm tol f seeds
  in head [ evs | evs <- stream, length evs >= dim ]

-- | Matrix-free Krylov route via 'constructEigenSystem' on @v -+> v@.
groundStateEigen
  :: forall v
   . ( FiniteDimensional v, LSpace v, InnerSpace v
     , Scalar v ~ Complex Double, RealFloat (RealPart (Scalar v)) )
  => Norm v -> (v -+> v) -> (Double, v)
groundStateEigen norm f =
  let tol = defaultEigenTolerance
      seeds = basisOf @v
      evs = iterate (finishEigenSystem norm)
            (completeEigenSystem norm tol f seeds)
            !! 2
  in case evs of
       [] -> error "GroundState.groundStateEigen: empty eigenvector set"
       eigenvectors ->
         let Eigenvector { ev_Eigenvalue = λ, ev_Eigenvector = vec } =
               minimumBy (comparing (realPart . ev_Eigenvalue)) eigenvectors
         in (realPart λ, vec)

spectrumEigen
  :: ( FiniteDimensional v, LSpace v, Scalar v ~ Complex Double
     , IEEE (RealPart (Scalar v)), RealFloat (RealPart (Scalar v))
     , Floating (Scalar v) )
  => Norm v -> (v +> v) -> [Double]
spectrumEigen norm f =
  sort [ realPart λ | (λ, _) <- eigen norm f ]

-- | Matrix-free Krylov ground state without 'FiniteDimensional'.
--
-- Supply at least one Krylov seed (e.g. the current centre-site tensor for DMRG).
-- When a canonical basis /is/ available, prefer 'groundStateEigen'.
groundStateKrylov
  :: forall v
   . ( LSpace v, InnerSpace v
     , Scalar v ~ Complex Double
     , RealFloat (RealPart (Scalar v))
     , Fractional (Scalar v), Floating (Scalar v) )
  => Norm v -> [v] -> (v -+> v) -> (Double, v)
groundStateKrylov norm seeds f =
  let tol = defaultEigenTolerance
      start =
        case [ evs' | evs' <- constructEigenSystem norm tol f seeds, not (null evs') ] of
          (initial : _) -> initial
          []            -> error "GroundState.groundStateKrylov: Krylov basis did not start (need seeds?)"
      refined = iterate (finishEigenSystem norm) start !! 2
  in case refined of
       [] -> error "GroundState.groundStateKrylov: empty eigenvector set"
       eigenvectors ->
         let Eigenvector { ev_Eigenvalue = λ, ev_Eigenvector = vec } =
               minimumBy (comparing (realPart . ev_Eigenvalue)) eigenvectors
         in (realPart λ, vec)

-- | 'groundStateKrylov' on @v +> v@ (cat-map endomorphisms).
groundStateKrylovMap
  :: forall v
   . ( LSpace v, InnerSpace v
     , Scalar v ~ Complex Double
     , RealFloat (RealPart (Scalar v))
     , Fractional (Scalar v), Floating (Scalar v) )
  => Norm v -> [v] -> (v +> v) -> (Double, v)
groundStateKrylovMap norm seeds = groundStateKrylov norm seeds . arr

-- | Lowest eigenpair of a Hermitian operator: @(eigenvalue, eigenvector)@.
groundState
  :: forall v. (FiniteDimensional v, InnerSpace v, Scalar v ~ Complex Double)
  => (v +> v) -> (Double, v)
groundState = groundStateDense

-- | Full (real) spectrum of a Hermitian operator, ascending.
spectrum
  :: ( FiniteDimensional v, InnerSpace v, Scalar v ~ Complex Double )
  => (v +> v) -> [Double]
spectrum = spectrumDense

-- | Map-space type matching a DMRG centre site @Centre 2 2 2@.
type Centre222 = (C 2 ⊗ C 2) +> C 2

randomComplexCoeffs :: Int -> StdGen -> ([Complex Double], StdGen)
randomComplexCoeffs n gen =
  foldr
    ( \_ (xs, g) ->
        let (re, g1) = randomR (-1, 1) g
            (im, g2) = randomR (-1, 1) g1
        in ((re :+ im) : xs, g2)
    )
    ([], gen)
    (replicate n ())

randomCentreVector :: StdGen -> (Centre222, StdGen)
randomCentreVector gen =
  let n = length (basisOf @Centre222)
      (coords, gen') = randomComplexCoeffs n gen
  in (fst (recomposeSB (entireBasis :: SubBasis Centre222) coords), gen')

randomCentreImages :: Int -> StdGen -> ([Centre222], StdGen)
randomCentreImages count gen =
  foldr
    ( \_ (xs, g) ->
        let (vec, g') = randomCentreVector g
        in (vec : xs, g')
    )
    ([], gen)
    (replicate count ())

endomorphismFromMatrix
  :: forall v
   . ( FiniteDimensional v, InnerSpace v, Scalar v ~ Complex Double )
  => H.Matrix (Complex Double) -> (v +> v)
endomorphismFromMatrix mat =
  let es = basisOf @v
      n = length es
      image j =
        sumV [ (mat `H.atIndex` (i, j)) *^ es !! i | i <- [0 .. n - 1] ]
  in fst (recomposeLinMap (entireBasis :: SubBasis v) [ image j | j <- [0 .. n - 1] ])

hermitianCentreOperator :: Centre222 +> Centre222 -> Centre222 +> Centre222
symmetricMatrix :: H.Matrix (Complex Double) -> H.Matrix (Complex Double)
symmetricMatrix mat =
  let ls = H.toLists mat
  in H.fromLists
       [ [ (ls !! i !! j + conjugate (ls !! j !! i)) / 2
         | j <- [0 .. length row - 1]
         ]
       | (i, row) <- zip [0 ..] ls
       ]

hermitianCentreOperator f =
  endomorphismFromMatrix (symmetricMatrix (toDenseMatrix f))

randomHermitianCentre :: StdGen -> (Centre222 +> Centre222, StdGen)
randomHermitianCentre gen =
  let n = length (basisOf @Centre222)
      (imgs, gen') = randomCentreImages n gen
      raw = fst (recomposeLinMap (entireBasis :: SubBasis Centre222) imgs)
  in (hermitianCentreOperator raw, gen')

-- | Smoke test: random Hermitian endomorphism on the @Centre 2 2 2@ map space,
-- comparing dense @eigSH@ against 'groundStateEigen'.
--
-- Run with @cabal run groundstate-smoke@, or from GHCi:
-- @smokeRandomEffectiveHamiltonian@.
--
-- For a network-contracted TFIM effective Hamiltonian, use
-- @scripts/effective_hamiltonian_smoke.hs@ instead (that module imports DMRG).
smokeRandomEffectiveHamiltonian :: IO ()
smokeRandomEffectiveHamiltonian = do
  gen <- newStdGen
  let dim = length (basisOf @Centre222)
      (heff, gen') = randomHermitianCentre gen
      f = arr heff
      (eDense, _) = groundStateDense heff
  eigenOutcome <- try (evaluate (groundStateEigen hilbertSchmidtNorm f))
  krylovOutcome <- try (evaluate (groundStateKrylov hilbertSchmidtNorm (basisOf @Centre222) f))
  putStrLn "Random Hermitian endomorphism on Centre 2 2 2 map space:"
  putStrLn $ "  Hilbert-space dimension = " ++ show dim
  putStrLn $ "  dense eigenvalue        = " ++ show eDense
  case eigenOutcome of
    Left (ex :: SomeException) ->
      putStrLn $ "  constructEigen CRASHED  = " ++ show ex
    Right (eEigen, _) -> do
      let diff = abs (eDense - eEigen)
      putStrLn $ "  constructEigen eigen    = " ++ show eEigen
      putStrLn $ "  |dense - krylov|        = " ++ show diff
      if diff <= 1e-8
        then putStrLn "  OK (within 1e-8)"
        else putStrLn "  MISMATCH — possible Krylov / norm bug"
  case krylovOutcome of
    Left (ex :: SomeException) ->
      putStrLn $ "  groundStateKrylov CRASHED = " ++ show ex
    Right (eKrylov, _) -> do
      let diff = abs (eDense - eKrylov)
      putStrLn $ "  innerProductNorm eigen  = " ++ show eKrylov
      putStrLn $ "  |dense - krylov'|       = " ++ show diff
      if diff <= 1e-8
        then putStrLn "  groundStateKrylov OK (within 1e-8)"
        else putStrLn "  groundStateKrylov MISMATCH"
  putStrLn $ "  seed follow-up gen tag  = " ++ show (fst (split gen'))
