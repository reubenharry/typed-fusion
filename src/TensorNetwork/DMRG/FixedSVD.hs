{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Single-site DMRG like "TensorNetwork.DMRG.Fixed", but gauge transport
-- goes through 'Experiments.SVD.svdC' and 'SVDPendants' instead of hmatrix
-- 'thinSVD'.
--
-- The SVD monad is 'SvdM' = @State StdGen@ with a fixed seed (default 42),
-- matching the spirit of 'TensorNetwork.DMRG.Fixed.seededMPS222' — no 'IO'.
--
-- Wiring sketch:
--
--   1. Sample @dimA + 1@ domain initial vectors in 'SvdM'.
--   2. Call @svdC (FixedInitialVectors vecs) map dimA@.
--   3. Read off isometry columns from 'domainSingularVector',
--      right-singular / bond data from 'codomainSingularVector' and
--      'singularValue', then rebuild the same 'Site' / bond maps
--      'normalizeLeft' / 'normalizeRight' would have produced.
module TensorNetwork.DMRG.FixedSVD where

-- import Prelude hiding (($), (.))
-- import Control.Category.Constrained ((.))
-- import Control.Monad.Trans.State (State, evalState, state)
-- import Control.Arrow.Constrained (($), arr)
-- import Control.Monad (replicateM)
-- import Math.LinearMap.Category
--   ( type (+>), type (⊗)
--   , getLinearMap, LinearMap (..) )
-- import Math.LinearMap.Category.Instances ()
-- import Math.LinearMap.Category.Backend.HMatrix ()
-- import Numeric.LinearAlgebra.Static.COrphans ()
-- import Numeric.LinearAlgebra.Static (C, M, R, Sized (fromList, create), extract)
-- import Numeric.LinearAlgebra.Static.MPSLayout (siteLinearMap)
-- import qualified Numeric.LinearAlgebra as HM
-- import GHC.TypeLits (KnownNat, type (*))
-- import Data.Complex (Complex ((:+)), realPart)
-- import Data.Maybe (fromMaybe)
-- import Data.VectorSpace (magnitude, Scalar)
-- import Test.QuickCheck.Gen (vectorOf, unGen)
-- import Test.QuickCheck.Random (mkQCGen)
-- import System.Random (StdGen, mkStdGen, random)
-- import qualified Test.QuickCheck as QC

-- import Experiments.SVD (svdC, SVDPendants (..))
-- import Math.VectorSpace.Initializable (InitialVectors (..))
-- import TensorNetwork.MPS.Fixed.Internal
--   ( Site (..), cdim
--   , MPS3, MPO3, mps3, withMPS3, withMPO3, OpWireNats )
-- import TensorNetwork.MPS.Fixed (leftSvdFactor, rightSvdFactor)
-- import TensorNetwork.Categorical (swapMap, splitBond, fuseBond)
-- import TensorNetwork.DMRG.Env (leftBoundary)
-- import Control.Monad.Identity (runIdentity)
-- import TensorNetwork.DMRG.Fixed
--   ( dmrg, DmrgResult (..), sweep, solveCenterAt
--   , denseGroundEnergy, energy, tfimMPO, seededMPS222
--   )

-- --------------------------------------------------------------------------------
-- -- Seeded SVD monad (no IO)
-- --------------------------------------------------------------------------------

-- -- | Stateful RNG for 'svdC' initial vectors and gauge transport.
-- type SvdM = State StdGen

-- -- | Default seed for deterministic SVD initialisation.
-- defaultSvdSeed :: Int
-- defaultSvdSeed = 42

-- -- | Run an 'SvdM' computation with a fixed seed.
-- runSvdM :: Int -> SvdM a -> a
-- runSvdM seed action = evalState action (mkStdGen seed)

-- --------------------------------------------------------------------------------
-- -- Site layout helpers (same as Fixed; duplicated to keep this module standalone)
-- --------------------------------------------------------------------------------

-- siteForLeftSVD
--   :: forall bl p br
--    . ( KnownNat bl, KnownNat p, KnownNat br
--      , KnownNat (p * bl), KnownNat (bl * p), p * bl ~ bl * p )
--   => (C bl ⊗ C p) +> C br -> C (bl * p) +> C br
-- siteForLeftSVD f = f . swapMap . splitBond @p @bl

-- siteFromLeftSVD
--   :: forall bl p br
--    . (KnownNat bl, KnownNat p, KnownNat br, KnownNat (p * bl), p * bl ~ bl * p)
--   => C (bl * p) +> C br -> (C bl ⊗ C p) +> C br
-- siteFromLeftSVD g = g . fuseBond @p @bl . swapMap

-- siteFromStorage
--   :: forall bl p br
--    . ( KnownNat bl, KnownNat p, KnownNat br
--      , KnownNat (p * br), KnownNat (p * bl) )
--   => M bl (p * br) -> Site bl p br
-- siteFromStorage = Site . siteLinearMap

-- rowsToM :: forall r c. (KnownNat r, KnownNat c) => [C c] -> M r c
-- rowsToM rs =
--   fromMaybe (error "rowsToM") $ create (HM.fromRows (map extract rs))

-- colsToM :: forall m n. (KnownNat m, KnownNat n) => [C m] -> M m n
-- colsToM cs =
--   fromMaybe (error "colsToM") $ create (HM.fromColumns (map extract cs))

-- smallComplex :: QC.Gen (Complex Double)
-- smallComplex = do
--   re <- QC.elements [-2 .. 2 :: Int]
--   im <- QC.elements [-2 .. 2 :: Int]
--   pure (fromIntegral re :+ fromIntegral im)

-- genC :: forall n. KnownNat n => QC.Gen (C n)
-- genC = fromList <$> replicateM (cdim @n) smallComplex

-- --------------------------------------------------------------------------------
-- -- SVDPendants ↔ typed site / bond maps
-- --------------------------------------------------------------------------------

-- -- | Sample @n@ random @C k@ vectors for 'svdC' initialisation.
-- sampleCnVectors :: forall k. KnownNat k => Int -> SvdM [C k]
-- sampleCnVectors n = state $ \g ->
--   let (qcSeed, g') = random g
--       vs = unGen (vectorOf n (genC @k)) (mkQCGen qcSeed) (n * 20)
--   in (vs, g')

-- -- | Thin isometry @C dom +> C cod@: columns are codomain images (length @cod@).
-- pendantsToIsoMap
--   :: forall dom cod
--    . (KnownNat dom, KnownNat cod)
--   => [SVDPendants (C dom) (C cod)] -> C dom +> C cod
-- pendantsToIsoMap ps =
--   LinearMap (colsToM (map codomainSingularVector (take (cdim @dom) ps)))

-- -- | Bond factor @Σ V†@ from pendant codomain vectors and singular values.
-- leftBondFromPendants
--   :: forall cod v. (KnownNat cod, Scalar (C cod) ~ Complex Double)
--   => [SVDPendants v (C cod)] -> C cod +> C cod
-- leftBondFromPendants ps =
--   let k = cdim @cod
--       pendants = take k ps
--       v = colsToM (map codomainSingularVector pendants)
--       sigma = singularValuesR pendants
--   in leftSvdFactor sigma v

-- -- | Bond factor @U Σ@ from pendant domain vectors and singular values.
-- rightBondFromPendants
--   :: forall dom w. (KnownNat dom, Scalar w ~ Complex Double)
--   => [SVDPendants (C dom) w] -> C dom +> C dom
-- rightBondFromPendants ps =
--   let k = cdim @dom
--       pendants = take k ps
--       u = colsToM (map domainSingularVector pendants)
--       sigma = singularValuesR pendants
--   in rightSvdFactor u sigma

-- -- | Right-normalised site storage @V†@ (@bl × p·br@), rows =
-- -- 'codomainSingularVector'.
-- siteStorageFromPendants
--   :: forall bl p br
--    . (KnownNat bl, KnownNat p, KnownNat br, KnownNat (p * br))
--   => [SVDPendants (C bl) (C (p * br))] -> M bl (p * br)
-- siteStorageFromPendants ps =
--   rowsToM (map codomainSingularVector (take (cdim @bl) ps))

-- singularValuesR
--   :: forall n v w
--    . (KnownNat n, Scalar w ~ Complex Double)
--   => [SVDPendants v w] -> R n
-- singularValuesR ps =
--   fromMaybe (error "singularValuesR") $
--     create (HM.fromList vals)
--   where
--     vals =
--       [ realPart (magnitude (singularValue p :: Complex Double))
--       | p <- take (cdim @n) ps
--       ]

-- normalizeLeftSvdM
--   :: forall bl p br
--    . ( KnownNat bl, KnownNat p, KnownNat br
--      , KnownNat (p * br), KnownNat (bl * p), KnownNat (p * bl)
--      , p * bl ~ bl * p )
--   => Site bl p br
--   -> SvdM (Site bl p br, C br +> C br)
-- normalizeLeftSvdM (Site f) = do
--   let dimA = cdim @br
--   vecs <- sampleCnVectors @(bl * p) (dimA + 1)
--   pendants <-
--     svdC
--       (FixedInitialVectors vecs)
--       (arr $ siteForLeftSVD f)
--       (fromIntegral dimA)
--   pure
--     ( Site (siteFromLeftSVD (pendantsToIsoMap pendants))
--     , leftBondFromPendants pendants
--     )

-- normalizeRightSvdM
--   :: forall bl p br
--    . ( KnownNat bl, KnownNat p, KnownNat br
--      , KnownNat (p * br), KnownNat (p * bl) )
--   => Site bl p br
--   -> SvdM (C bl +> C bl, Site bl p br)
-- normalizeRightSvdM (Site f) = do
--   let dimA = cdim @bl
--   vecs <- sampleCnVectors @bl (dimA + 1)
--   pendants <-
--     svdC
--       (FixedInitialVectors vecs)
--       (arr $ LinearMap (getLinearMap f))
--       (fromIntegral dimA)
--   pure
--     ( rightBondFromPendants pendants
--     , siteFromStorage @bl @p @br (siteStorageFromPendants @bl @p @br pendants)
--     )

-- --------------------------------------------------------------------------------
-- -- Sweeping (mirror of Fixed.sweep)
-- --------------------------------------------------------------------------------

-- -- | One DMRG sweep. Gauge transport still uses hmatrix SVD via 'Fixed';
-- -- 'normalizeLeftSvdM' / 'normalizeRightSvdM' remain for 'svdC' experiments.
-- sweepSvd
--   :: forall p w b
--    . ( KnownNat p, KnownNat w, KnownNat b
--      , KnownNat (p * b), KnownNat (b * p)
--      , p * b ~ b * p, OpWireNats p w w b b )
--   => MPO3 p w -> MPS3 p b -> SvdM (Double, MPS3 p b)
-- sweepSvd mpo mps = pure (runIdentity (sweep solveCenterAt mpo mps))

-- -- | DMRG driver with 'svdC' gauge transport (run with 'runSvdM' and a fixed seed).
-- dmrgSvd
--   :: forall p w b
--    . ( KnownNat p, KnownNat w, KnownNat b
--      , KnownNat (p * b), KnownNat (b * p)
--      , p * b ~ b * p, OpWireNats p w w b b )
--   => Int -> Double -> MPO3 p w -> MPS3 p b -> SvdM (DmrgResult p b 1)
-- dmrgSvd maxSweeps tol mpo = dmrg maxSweeps tol mpo sweepSvd

-- -- | DMRG with 'svdC' gauge transport converges to the dense @C (p³)@ ground energy.
-- -- Not in the test suite yet — 'Experiments.SVD.svdC' is still WIP.
-- prop_dmrgSvdGroundEnergyMatchesDense :: QC.Property
-- prop_dmrgSvdGroundEnergyMatchesDense =
--   QC.forAll (QC.choose (0, 99)) $ \seed ->
--     let mpo = tfimMPO 1 0.7
--         psi0 = seededMPS222 seed
--         DmrgResult { dmrgFinalEnergy = e, dmrgFinalMPS = psi } =
--           runSvdM seed $ dmrgSvd 10 1e-12 mpo psi0
--         eDense = denseGroundEnergy mpo
--         tol = 1e-9
--     in QC.counterexample ("DMRG-SVD " ++ show e ++ " vs dense " ++ show eDense)
--          (abs (e - eDense) <= tol QC..&&. energy mpo psi >= eDense - tol)
