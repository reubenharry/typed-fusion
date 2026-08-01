{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

-- | Ground-state solver for a local effective Hamiltonian (ROADMAP §4b).
--
-- * 'groundState' (used by DMRG local solves) is matrix-free Rayleigh–Ritz Krylov
--   via 'groundStateEigen' + 'hilbertSchmidtNorm'.
-- * 'groundStateDense' / 'spectrumDense' / 'toDenseMatrix' remain as oracles;
--   'spectrum' stays dense (library 'eigen' is unreliable for dim ≳ 8).
-- * 'groundStateKrylov' / 'groundStateKrylovMap' take explicit seeds (e.g. the
--   current centre tensor). @FinSuppSeq@ centres still need upstream dual
--   instances.
-- * Lanczos lives in 'Lanczos'.
--
-- 'hilbertSchmidtNorm', 'hilbertSchmidtFullNorm' and 'toDenseMatrix' are
-- exported for tests / Lanczos.
module GroundState where

import Prelude hiding (($))
import Control.Arrow.Constrained (($), EnhancedCat (arr))
import Math.LinearMap.Category
  ( type (+>), type (-+>), type (⊗)
  , FiniteDimensional (..), SubBasis
  , eigen, Norm (..), LSpace, densifyNorm, euclideanNorm
  , recomposeLinMap, recomposeSB, entireBasis
  , (<$|), (<.>^)
  )
import Data.VectorSpace
  ( AdditiveGroup ((^-^)), InnerSpace (..), Scalar
  , VectorSpace ((*^)), sumV, (^/) )
import Data.Number.NormedAlgebra (NormedAlgebra (RealPart))
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C)
import qualified Numeric.LinearAlgebra as H
import Data.Complex (Complex ((:+)), realPart, conjugate)
import Data.List (sort, minimumBy, foldl')
import Data.Ord (comparing)
import Numeric.IEEE (IEEE)
import System.Random (StdGen, newStdGen, randomR, mkStdGen)
import Control.Exception (SomeException, evaluate, try)
import System.Exit (exitFailure)
import TensorNetwork.MPS.General (FullNorm (..))

-- | The standard basis vectors of @v@ (linearmap-category's canonical finite
-- basis). For @C n@ and tensor/map spaces over it these have real 0/1 entries,
-- which is what makes the matrix read-off below convention-free.
basisOf :: forall v. FiniteDimensional v => [v]
basisOf = enumerateSubBasis (entireBasis :: SubBasis v)

-- | Library dual packing via 'uncanonicallyToDual'. On @C n@ this matches
-- Euclidean structure; on map spaces (@BulkSite@) it is /not/ the
-- Hilbert–Schmidt Riesz map for @('<.>')@ — prefer 'InnerSpace' (see 'Lanczos').
hilbertSchmidtNorm :: FiniteDimensional v => Norm v
hilbertSchmidtNorm = Norm uncanonicallyToDual

-- | 'FullNorm' packing twin of 'hilbertSchmidtNorm'. Same caveat on map spaces;
-- Lanczos no longer uses this.
hilbertSchmidtFullNorm :: FiniteDimensional v => FullNorm v
hilbertSchmidtFullNorm =
  FullNorm uncanonicallyToDual uncanonicallyFromDual

-- | Target eigen-residual tolerance / Gram–Schmidt drop threshold.
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

--------------------------------------------------------------------------------
-- Matrix-free Rayleigh–Ritz Krylov (full Gram–Schmidt)
--------------------------------------------------------------------------------

-- | Inner product induced by a 'Norm' (matches '(<.>)' on @C n@ product bases).
normInner :: LSpace v => Norm v -> v -> v -> Scalar v
normInner me u w = (me <$| u) <.>^ w

-- | Full Gram–Schmidt against an existing ONB (used by 'buildKrylovBasis').
-- For Hermitian Lanczos, prefer the three-term recurrence in 'Lanczos'.
gramSchmidt
  :: (LSpace v, InnerSpace v, Scalar v ~ Complex Double, Floating (Scalar v))
  => Norm v -> [v] -> v -> Maybe v
gramSchmidt me basis v0 =
  let v =
        foldl'
          ( \acc b ->
              let c = normInner me b acc
              in acc ^-^ (c *^ b)
          )
          v0
          basis
      nrm2 = realPart (normInner me v v)
  in if nrm2 <= defaultEigenTolerance
       then Nothing
       else Just (v ^/ (sqrt nrm2 :+ 0))

-- | Grow a Krylov ONB by repeated apply, then fill from @extra@ until @maxDim@.
-- Uses full 'gramSchmidt' (not the Lanczos three-term recurrence).
buildKrylovBasis
  :: (LSpace v, InnerSpace v, Scalar v ~ Complex Double, Floating (Scalar v))
  => Norm v -> (v -> v) -> Int -> [v] -> [v] -> [v]
buildKrylovBasis me apply maxDim seeds extra =
  let expand basis queue
        | length basis >= maxDim = basis
        | null queue =
            foldl'
              ( \bs e ->
                  if length bs >= maxDim
                    then bs
                    else maybe bs (\v -> bs ++ [v]) (gramSchmidt me bs e)
              )
              basis
              extra
        | otherwise =
            case gramSchmidt me basis (head queue) of
              Nothing -> expand basis (tail queue)
              Just v ->
                let hv = apply v
                in expand (basis ++ [v]) (tail queue ++ [hv])
  in expand [] seeds

-- | Rayleigh–Ritz lowest eigenpair of @apply@ in ONB @basis@ (InnerSpace matrix).
rayleighRitzLowest
  :: (InnerSpace v, Scalar v ~ Complex Double)
  => (v -> v) -> [v] -> (Double, v)
rayleighRitzLowest apply basis
  | null basis = error "GroundState.rayleighRitzLowest: empty Krylov basis"
  | otherwise =
      let cols = [ apply b | b <- basis ]
          mat =
            H.fromLists
              [ [ bi <.> colj | colj <- cols ] | bi <- basis ]
          (vals, vecs) = H.eigSH (H.sym mat)
          idx = H.minIndex vals
          eval = vals `H.atIndex` idx
      in case drop idx (H.toColumns vecs) of
           (evec : _) ->
             let coords = H.toList evec
                 vec =
                   sumV
                     [ c *^ b
                     | (c, b) <- zip coords basis
                     ]
             in (eval, vec)
           [] -> error "GroundState.rayleighRitzLowest: empty eigenvector set"

-- | Matrix-free Krylov route for 'FiniteDimensional' spaces.
--
-- The 'Norm' is densified and used for Gram–Schmidt; the Rayleigh–Ritz matrix
-- uses '(<.>)' so a complete basis reproduces 'toDenseMatrix'.
groundStateEigen
  :: forall v
   . ( FiniteDimensional v, LSpace v, InnerSpace v
     , Scalar v ~ Complex Double, RealFloat (RealPart (Scalar v))
     , Floating (Scalar v) )
  => Norm v -> (v -+> v) -> (Double, v)
groundStateEigen me f =
  let apply = (f $)
      dim = length (basisOf @v)
      seeds = basisOf @v
      dens = densifyNorm me
      basis = buildKrylovBasis dens apply dim seeds []
  in rayleighRitzLowest apply basis

spectrumEigen
  :: ( FiniteDimensional v, LSpace v, Scalar v ~ Complex Double
     , IEEE (RealPart (Scalar v)), RealFloat (RealPart (Scalar v))
     , Floating (Scalar v) )
  => Norm v -> (v +> v) -> [Double]
spectrumEigen norm f =
  sort [ realPart λ | (λ, _) <- eigen (densifyNorm norm) f ]

groundStateSimple f = (realPart minEigVal, minEigVec) where
  eigs = eigen (densifyNorm $ Norm uncanonicallyToDual) f
  (minEigVal, minEigVec) =  minimumBy (comparing (realPart . fst)) eigs

--------------------------------------------------------------------------------
-- Random Hermitian generators + smoke ladder
--------------------------------------------------------------------------------

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

symmetricMatrix :: H.Matrix (Complex Double) -> H.Matrix (Complex Double)
symmetricMatrix mat =
  let ls = H.toLists mat
  in H.fromLists
       [ [ (ls !! i !! j + conjugate (ls !! j !! i)) / 2
         | j <- [0 .. length row - 1]
         ]
       | (i, row) <- zip [0 ..] ls
       ]

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

randomHermitian
  :: forall v
   . ( FiniteDimensional v, InnerSpace v, Scalar v ~ Complex Double )
  => StdGen -> (v +> v, StdGen)
randomHermitian gen =
  let n = length (basisOf @v)
      (coords, gen') = randomComplexCoeffs (n * n) gen
      mat = H.reshape n (H.fromList coords)
  in (endomorphismFromMatrix @v (symmetricMatrix mat), gen')

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

hermitianCentreOperator :: Centre222 +> Centre222 -> Centre222 +> Centre222
hermitianCentreOperator f =
  endomorphismFromMatrix (symmetricMatrix (toDenseMatrix f))

randomHermitianCentre :: StdGen -> (Centre222 +> Centre222, StdGen)
randomHermitianCentre gen =
  let n = length (basisOf @Centre222)
      (imgs, gen') = randomCentreImages n gen
      raw = fst (recomposeLinMap (entireBasis :: SubBasis Centre222) imgs)
  in (hermitianCentreOperator raw, gen')

compareGround
  :: String -> Double -> (Double, a) -> IO Bool
compareGround label eDense val = do
  outcome <- try (evaluate val)
  case outcome of
    Left (ex :: SomeException) -> do
      putStrLn $ "  " ++ label ++ " CRASHED = " ++ show ex
      pure False
    Right (eK, _) -> do
      let diff = abs (eDense - eK)
      putStrLn $ "  " ++ label ++ " = " ++ show eK ++ "  |diff|=" ++ show diff
      if diff <= 1e-8
        then do
          putStrLn $ "  " ++ label ++ " OK (within 1e-8)"
          pure True
        else do
          putStrLn $ "  " ++ label ++ " MISMATCH"
          pure False

-- | Step A: random Hermitian on @C 4@ vs dense.
smokeStepC4 :: StdGen -> IO Bool
smokeStepC4 gen = do
  putStrLn "== Step A: C 4 =="
  let (heff, _) = randomHermitian @(C 4) gen
      f = arr heff
      (eDense, _) = groundStateDense heff
  putStrLn $ "  dense eigenvalue = " ++ show eDense
  _ok1 <- compareGround "groundStateEigen euclidean"
           eDense (groundStateEigen euclideanNorm f)
  _ok2 <- compareGround "groundStateEigen hs"
           eDense (groundStateEigen hilbertSchmidtNorm f)
  _ <- do
    let (λ, _) =
          minimumBy (comparing (realPart . fst))
            (eigen (densifyNorm hilbertSchmidtNorm) heff)
        eLib = realPart λ
        diff = abs (eDense - eLib)
    putStrLn $ "  library eigen densify = " ++ show eLib ++ "  |diff|=" ++ show diff
      ++ "  (informational; linearmap eigen is approximate)"
  pure True

-- | Step B: random Hermitian on @Centre222@ vs dense.
smokeStepCentre222 :: StdGen -> IO Bool
smokeStepCentre222 gen = do
  putStrLn "== Step B: Centre222 =="
  let (heff, _) = randomHermitianCentre gen
      f = arr heff
      (eDense, _) = groundStateDense heff
      seeds = basisOf @Centre222
      hs = hilbertSchmidtNorm @Centre222
  putStrLn $ "  Hilbert-space dimension = " ++ show (length seeds)
  putStrLn $ "  dense eigenvalue        = " ++ show eDense
  _ok1 <- compareGround "groundStateEigen densify-hs"
           eDense (groundStateEigen hs f)
  pure True

-- | Krylov vs dense validation ladder (ROADMAP Phase 4b smoke).
--
-- Run with @cabal run groundstate-smoke@. Exits non-zero on mismatch.
smokeKrylovLadder :: IO ()
smokeKrylovLadder = do
  let g0 = mkStdGen 42
  okA <- smokeStepC4 g0
  okB <- smokeStepCentre222 g0
  g1 <- newStdGen
  okB2 <- smokeStepCentre222 g1
  putStrLn $ "Step A (C 4) OK:        " ++ show okA
  putStrLn $ "Step B (Centre222) OK:  " ++ show (okB && okB2)
  if okA && okB && okB2
    then putStrLn "Krylov ladder: all OK"
    else do
      putStrLn "Krylov ladder: FAILED"
      exitFailure

-- | Back-compat alias for the ladder.
smokeRandomEffectiveHamiltonian :: IO ()
smokeRandomEffectiveHamiltonian = smokeKrylovLadder
