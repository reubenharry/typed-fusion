{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}

-- | Performance probes for the MPS / DMRG hot path.
--
--   cabal bench quantum-bench --benchmark-options='--verbosity=1'
--
-- Groups:
--   * mpsInner / mpsMPOInner — should be ~linear in bulk length @n@
--   * envRebuild — current DMRG rebuilds L/R from scratch per site (~quadratic)
--   * heffApply / eigensolve — local centre cost (χ=3, p=2, q=1)
--   * regauge — polar / mixed-canonical (q=1)
--   * dmrg — solveBulk / sweep / short dmrg
module Main where

import Prelude hiding (($), (.))
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($))
import Control.Lens ((^.), _1)
import Criterion.Main
import Data.Complex (realPart)
import Data.Proxy (Proxy (..))
import Data.VectorSpace (InnerSpace ((<.>)), AdditiveGroup (zeroV))
import GHC.TypeNats (KnownNat, natVal)
import Numeric.LinearAlgebra.Static (C, fromList)

import GroundState (groundState)
import Math.LinearMap.Category (type (+>), type (⊗))
import TensorNetwork.DMRG.Env
  ( LeftMPOEnv, RightMPOEnv, leftEnvBeforeBulk, rightEnvAfterBulk )
import TensorNetwork.DMRG.Fixed
  ( DmrgResult (..), dmrg, energy, heffBulk, productMPS, solveBulk, sweep
  , tfimMPO
  )
import TensorNetwork.MPS.General
  ( FullNorm, MPS, MPO, hermitianNorm, mixedCanonicalCentre3
  , mpsBulk, mpsInner, mpsLeft, mpsMPOInner, mpsRight, polarLeftSite
  , polarRightSite, svdSplit
  )

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

nb :: FullNorm (C 3)
nb = hermitianNorm

np :: FullNorm (C 2)
np = hermitianNorm

nSites :: forall n. KnownNat n => Int
nSites = fromIntegral (natVal (Proxy @n))

-- | Force a left MPO environment by applying it to a bond basis vector.
forceLeftEnv :: LeftMPOEnv (C 3) -> Double
forceLeftEnv e =
  let v = e $ (fromList [1, 0, 0] :: C 3)
  in realPart (v <.> v)

-- | Force a right MPO environment by applying it to a product bond vector.
forceRightEnv :: RightMPOEnv (C 3) -> Double
forceRightEnv e =
  let v = e $ (zeroV :: C 3 ⊗ C 3)
  in realPart (v <.> v)

-- | Force a small endomorphism by Frobenius self-overlap of one column image.
forceEndo :: (C 2 +> C 3) -> Double
forceEndo m =
  let v = m $ (fromList [1, 0] :: C 2)
  in realPart (v <.> v)

withChain
  :: forall n. KnownNat n
  => (MPS (C 3) (C 2) n -> MPO (C 3) n (C 2) (C 2) -> Benchmark)
  -> Benchmark
withChain k =
  let psi = productMPS @n
      mpo = tfimMPO @n 1.0 0.7
  in k psi mpo

--------------------------------------------------------------------------------
-- mpsInner / mpsMPOInner (expect ~O(n))
--------------------------------------------------------------------------------

benchInner :: forall n. KnownNat n => Benchmark
benchInner = withChain @n $ \psi _ ->
  bench ("n=" ++ show (nSites @n)) $
    whnf (\p -> realPart (mpsInner nb np p p)) psi

benchMPOInner :: forall n. KnownNat n => Benchmark
benchMPOInner = withChain @n $ \psi mpo ->
  bench ("n=" ++ show (nSites @n)) $
    whnf (\p -> realPart (mpsMPOInner nb np p mpo p)) psi

benchEnergy :: forall n. KnownNat n => Benchmark
benchEnergy = withChain @n $ \psi mpo ->
  bench ("n=" ++ show (nSites @n)) $
    whnf (\p -> energy nb np mpo p) psi

--------------------------------------------------------------------------------
-- Environment rebuild (current DMRG is ~O(n²) per sweep)
--------------------------------------------------------------------------------

benchLeftEnvFull :: forall n. KnownNat n => Benchmark
benchLeftEnvFull = withChain @n $ \psi mpo ->
  bench ("n=" ++ show (nSites @n)) $
    whnf (\p -> forceLeftEnv (leftEnvBeforeBulk nb np (nSites @n) p mpo)) psi

benchRightEnvFull :: forall n. KnownNat n => Benchmark
benchRightEnvFull = withChain @n $ \psi mpo ->
  bench ("n=" ++ show (nSites @n)) $
    whnf (\p -> forceRightEnv (rightEnvAfterBulk nb np (-1) p mpo)) psi

-- | Rebuild L and R for every bulk site — mirrors 'solveAllSites' env work.
benchEnvAllSites :: forall n. KnownNat n => Benchmark
benchEnvAllSites = withChain @n $ \psi mpo ->
  bench ("n=" ++ show (nSites @n)) $
    whnf
      ( \p ->
          sum
            [ forceLeftEnv (leftEnvBeforeBulk nb np j p mpo)
                + forceRightEnv (rightEnvAfterBulk nb np j p mpo)
            | j <- [0 .. nSites @n - 1]
            ]
      )
      psi

--------------------------------------------------------------------------------
-- Local Heff apply + eigensolve (q = 1)
--------------------------------------------------------------------------------

benchHeffApply :: Benchmark
benchHeffApply =
  let psi = productMPS @1
      mpo = tfimMPO @1 1.0 0.7
      heff = heffBulk nb np 0 psi mpo
      centre = psi ^. mpsBulk . _1
  in bench "y<.>Heff x" $
       whnf (\c -> realPart (c <.> (heff $ c))) centre

-- | 'groundState' seeds the full canonical basis then builds Krylov to dim —
-- effectively dense cost on the centre (dim = χ² p = 18 for χ=3,p=2).
benchEigensolve :: Benchmark
benchEigensolve =
  let psi = productMPS @1
      mpo = tfimMPO @1 1.0 0.7
      heff = heffBulk nb np 0 psi mpo
  in bench "groundState heffBulk" $
       whnf (fst . groundState) heff

benchSolveBulk :: Benchmark
benchSolveBulk =
  let psi = productMPS @1
      mpo = tfimMPO @1 1.0 0.7
  in bench "solveBulk j=0" $
       whnf (\p -> fst (solveBulk @3 @2 @1 nb np 0 mpo p)) psi

--------------------------------------------------------------------------------
-- Regauging (q = 1)
--------------------------------------------------------------------------------

benchMixedCanonical :: Benchmark
benchMixedCanonical =
  let psi = productMPS @1
  in bench "mixedCanonicalCentre3" $
       whnf
         ( \p ->
             let g = mixedCanonicalCentre3 p
                 c = g ^. mpsBulk . _1
             in realPart (c <.> c)
         )
         psi

benchPolarLeft :: Benchmark
benchPolarLeft =
  let l = productMPS @1 ^. mpsLeft
  in bench "polarLeftSite" $
       whnf (\a -> forceLeftBond (fst (polarLeftSite a))) l
  where
    forceLeftBond m =
      let v = m $ (fromList [1, 0, 0] :: C 3)
      in realPart (v <.> v)

benchPolarRight :: Benchmark
benchPolarRight =
  let r = productMPS @1 ^. mpsRight
  in bench "polarRightSite" $
       whnf
         ( \b ->
             let iso = fst (polarRightSite b)  -- C 3 +> C 2
                 v = iso $ (fromList [1, 0, 0] :: C 3)
             in realPart (v <.> v)
         )
         r

benchSvdSplit :: Benchmark
benchSvdSplit =
  let l = productMPS @1 ^. mpsLeft  -- C 2 +> C 3
  in bench "svdSplit (left site)" $
       whnf (\a -> forceEndo (fst (svdSplit @2 @3 @3 a))) l

--------------------------------------------------------------------------------
-- End-to-end DMRG pieces (q = 1; longer chains lack gauge transport)
--------------------------------------------------------------------------------

benchSweep :: Benchmark
benchSweep =
  let psi = productMPS @1
      mpo = tfimMPO @1 1.0 0.7
  in bench "sweep q=1" $
       whnf (\p -> fst (sweep @3 @2 @1 mpo p)) psi

benchDmrgShort :: Benchmark
benchDmrgShort =
  let psi = productMPS @1
      mpo = tfimMPO @1 1.0 0.7
  in bench "dmrg 2 sweeps" $
       whnf (\p -> dmrgFinalEnergy (dmrg @3 @2 @1 2 1e-6 mpo p)) psi

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main =
  defaultMain
    [ bgroup "mpsInner"
        [ benchInner @1
        , benchInner @10
        , benchInner @50
        , benchInner @100
        , benchInner @500
        , benchInner @1000
        ]
    , bgroup "mpsMPOInner"
        [ benchMPOInner @1
        , benchMPOInner @10
        , benchMPOInner @50
        , benchMPOInner @100
        , benchMPOInner @500
        , benchMPOInner @1000
        ]
    , bgroup "energy"
        [ benchEnergy @1
        , benchEnergy @10
        , benchEnergy @50
        , benchEnergy @100
        ]
    , bgroup "leftEnvFull"
        [ benchLeftEnvFull @1
        , benchLeftEnvFull @10
        , benchLeftEnvFull @50
        , benchLeftEnvFull @100
        ]
    , bgroup "rightEnvFull"
        [ benchRightEnvFull @1
        , benchRightEnvFull @10
        , benchRightEnvFull @50
        , benchRightEnvFull @100
        ]
    , bgroup "envAllSites (DMRG-shaped)"
        [ benchEnvAllSites @1
        , benchEnvAllSites @5
        , benchEnvAllSites @10
        , benchEnvAllSites @20
        , benchEnvAllSites @40
        ]
    , bgroup "localSolve"
        [ benchHeffApply
        , benchEigensolve
        , benchSolveBulk
        ]
    , bgroup "regauge"
        [ benchMixedCanonical
        , benchPolarLeft
        , benchPolarRight
        , benchSvdSplit
        ]
    , bgroup "dmrg"
        [ benchSweep
        , benchDmrgShort
        ]
    ]
