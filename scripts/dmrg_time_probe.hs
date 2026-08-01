{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Micro-timings for the 3-site TFIM DMRG path (forces each stage).
--   cabal run dmrg-time-probe
import Prelude hiding (($), (.))
import Control.Arrow.Constrained (($), arr)
import Control.Category.Constrained ((.))
import Control.Exception (evaluate)
import Control.Lens ((^.), _1)
import Data.Complex (realPart)
import qualified Data.List.NonEmpty as NE
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import Data.VectorSpace (InnerSpace ((<.>)))
import Text.Printf (printf)

import Lanczos
  ( defaultLanczosTolerance, groundStateLanczos
  , lanczosLowestQ, lanczosQ, lanczosTridiag
  )
import TensorNetwork.DMRG.Chain (getBulk)
import TensorNetwork.DMRG.Env
  ( leftEnvBeforeBulk, rightEnvAfterBulk
  )
import TensorNetwork.DMRG.Fixed
  ( centreDimBulk, dmrg, dmrgFinalEnergy, dmrgSweepEnergies, energy
  , heffBulk, heffLeft, heffRight, productMPS, solveBulk, solveLeft
  , solveRight, sweep, tfimMPO
  )
import TensorNetwork.MPS.General
  ( effectiveHBulk, hermitianNorm, mixedCanonicalCentre3
  , mixedCanonicalLeft3, mixedCanonicalRight3, mpsBulk, mpsInner
  , mpsLeft, mpsMPOInner, mpsRight, mpoBulk
  )

timeIO :: String -> IO a -> IO a
timeIO label act = do
  t0 <- getCurrentTime
  a <- act
  t1 <- getCurrentTime
  printf "%-40s %8.3f ms\n" label (1000 * realToFrac (diffUTCTime t1 t0) :: Double)
  pure a

-- | Force a scalar result (and thus the thunks feeding it).
forceReal :: Double -> IO Double
forceReal x = evaluate x

main :: IO ()
main = do
  let nb = hermitianNorm
      np = hermitianNorm
      mpo = tfimMPO @1 1 0.7
      psi0 = productMPS @1

  putStrLn "== contractions on productMPS =="
  z0 <- timeIO "1× mpsInner" $ forceReal (realPart (mpsInner nb np psi0 psi0))
  _  <- timeIO "1× mpsMPOInner" $ forceReal (realPart (mpsMPOInner nb np psi0 mpo psi0))
  e0 <- timeIO "1× energy" $ forceReal (energy nb np mpo psi0)
  printf "  ‖ψ‖²≈%s  E≈%s\n" (show z0) (show e0)

  putStrLn "\n== gauges =="
  psiL <- timeIO "mixedCanonicalLeft3 (force via mpsInner)" $ do
    let p = mixedCanonicalLeft3 psi0
    _ <- forceReal (realPart (mpsInner nb np p p))
    pure p
  psiC <- timeIO "mixedCanonicalCentre3 (force via mpsInner)" $ do
    let p = mixedCanonicalCentre3 psiL
    _ <- forceReal (realPart (mpsInner nb np p p))
    pure p
  _psiR <- timeIO "mixedCanonicalRight3 (force via mpsInner)" $ do
    let p = mixedCanonicalRight3 psiC
    _ <- forceReal (realPart (mpsInner nb np p p))
    pure p

  putStrLn "\n== environment builds (centre-gauged product) =="
  let c0 = psiC ^. mpsBulk . _1
  lEnv <- timeIO "leftEnvBeforeBulk 0" $ do
    let l = leftEnvBeforeBulk nb np 0 psiC mpo
    -- force: apply env in a scalar sandwich via Heff path pieces
    _ <- forceReal (realPart (c0 <.> c0))
    pure l
  rEnv <- timeIO "rightEnvAfterBulk 0" $ do
    let r = rightEnvAfterBulk nb np 0 psiC mpo
    pure r
  -- Force envs by one Heff apply built from them
  _ <- timeIO "effectiveHBulk first apply (forces L,R,op)" $ do
    let op = getBulk @1 0 (mpo ^. mpoBulk)
        y = effectiveHBulk lEnv op rEnv c0
    forceReal (realPart (c0 <.> y))
  _ <- timeIO "effectiveHBulk apply ×20 (envs hot)" $ do
    let op = getBulk @1 0 (mpo ^. mpoBulk)
        go 0 acc = acc
        go k acc = go (k - 1) (realPart (c0 <.> effectiveHBulk lEnv op rEnv c0) + acc)
    forceReal (go (20 :: Int) 0)

  putStrLn "\n== Heff endomorphism (construct = env build) =="
  heff <- timeIO "heffBulk construct (thunk)" $ evaluate (heffBulk nb np 0 psiC mpo)
  _ <- timeIO "heffBulk first apply" $ forceReal (realPart (c0 <.> (heff $ c0)))
  _ <- timeIO "heffBulk apply ×50" $
    forceReal (last [ realPart (c0 <.> (heff $ c0)) | _ <- [1 .. 50 :: Int] ])

  putStrLn "\n== Lanczos (envs already forced above) =="
  let dim = centreDimBulk @3 @2
      f = arr heff
  steps <- timeIO "lanczosTridiag (force all steps)" $ do
    let s = NE.fromList (NE.take dim (lanczosTridiag f c0))
    _ <- forceReal (fromIntegral (NE.length s))
    -- force last beta
    _ <- forceReal (realPart ((lanczosQ (NE.last s)) <.> (lanczosQ (NE.last s))))
    pure s
  printf "  Krylov length = %d\n" (NE.length steps)
  _ <- timeIO "lanczosLowestQ" $ do
    let (lam, v) = lanczosLowestQ f steps defaultLanczosTolerance
    _ <- forceReal (realPart (v <.> v))
    forceReal lam
  _ <- timeIO "groundStateLanczos" $ do
    let (lam, v) = groundStateLanczos dim c0 heff
    _ <- forceReal (realPart (v <.> v))
    forceReal lam

  putStrLn "\n== site solves (each stage forced) =="
  let psiLg = mixedCanonicalLeft3 psi0
  _ <- timeIO "force left gauge" $ forceReal (realPart (mpsInner nb np psiLg psiLg))
  heffL <- timeIO "heffLeft first apply" $ do
    let h = heffLeft nb np psiLg mpo
        s = psiLg ^. mpsLeft
    forceReal (realPart (s <.> (h $ s))) >> pure h
  (lamL, psiL1) <- timeIO "solveLeft (Lanczos only; Heff hot)" $ do
    -- rebuild like solveLeft but reuse timing separation: full solveLeft
    let (e, m) = solveLeft nb np mpo psiLg
    _ <- forceReal e
    _ <- forceReal (realPart (mpsInner nb np m m))
    pure (e, m)
  eL <- timeIO "energy(ψ after left)" $ forceReal (energy nb np mpo psiL1)
  printf "  λL=%s E=%s\n" (show lamL) (show eL)

  let psiCg = mixedCanonicalCentre3 psiL1
  _ <- timeIO "force centre gauge" $ forceReal (realPart (mpsInner nb np psiCg psiCg))
  heffC <- timeIO "heffBulk first apply (post-left)" $ do
    let h = heffBulk nb np 0 psiCg mpo
        s = psiCg ^. mpsBulk . _1
    forceReal (realPart (s <.> (h $ s))) >> pure h
  (lamC, psiC1) <- timeIO "solveBulk full" $ do
    let (e, m) = solveBulk nb np 0 mpo psiCg
    _ <- forceReal e
    _ <- forceReal (realPart (mpsInner nb np m m))
    pure (e, m)
  eC <- timeIO "energy(ψ after bulk)" $ forceReal (energy nb np mpo psiC1)
  printf "  λC=%s E=%s\n" (show lamC) (show eC)

  let psiRg = mixedCanonicalRight3 psiC1
  _ <- timeIO "force right gauge" $ forceReal (realPart (mpsInner nb np psiRg psiRg))
  _ <- timeIO "heffRight first apply" $ do
    let h = heffRight nb np psiRg mpo
        s = psiRg ^. mpsRight
    forceReal (realPart (s <.> (h $ s)))
  (lamR, psiR1) <- timeIO "solveRight full" $ do
    let (e, m) = solveRight nb np mpo psiRg
    _ <- forceReal e
    _ <- forceReal (realPart (mpsInner nb np m m))
    pure (e, m)
  eR <- timeIO "energy(ψ after right)" $ forceReal (energy nb np mpo psiR1)
  printf "  λR=%s E=%s\n" (show lamR) (show eR)

  putStrLn "\n== sweep / dmrg (includes double energy + traceM) =="
  (_psi, es) <- timeIO "sweep ×1" $ do
    let (p, e) = sweep mpo psi0
    _ <- forceReal (last e)
    pure (p, e)
  printf "  energies = %s\n" (show es)
  r <- timeIO "dmrg 2 sweeps" $ do
    let res = dmrg @3 @2 @1 2 1e-6 mpo psi0
    _ <- forceReal (dmrgFinalEnergy res)
    pure res
  printf "  final = %s\n" (show (dmrgFinalEnergy r))
  printf "  hist  = %s\n" (show (dmrgSweepEnergies r))

  putStrLn "\n== note =="
  putStrLn "solveAllSites: tell energy + traceM energy = 2× per site"
  putStrLn "3 sites × 2 sweeps × 2 = 12 energy evals inside dmrg"
  pure (heffL `seq` heffC `seq` ())
