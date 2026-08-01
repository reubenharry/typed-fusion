{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Steps 2–3 of the Heff diagnostic:
--
--   (2)  y <.> Heff x  ==  trace (Heff x ∘ siteDagger y)
--   (3)  trace (Heff x ∘ siteDagger y)  ==  effectiveHBulkInner y x
--
--   cabal run heff-hs-vs-network
import Prelude hiding (($), (.))
import Control.Category.Constrained ((.))
import qualified Control.Category.Constrained as Cat
import Control.Arrow.Constrained (($))
import Control.Lens ((^.), _1)
import Data.Complex (Complex, magnitude, realPart)
import Data.Proxy (Proxy (..))
import Data.VectorSpace (InnerSpace ((<.>)), (^-^))
import GHC.TypeLits (KnownNat, natVal, type (*))
import Math.LinearMap.Category (type (+>), type (⊗), trace)
import Numeric.LinearAlgebra.Static (C)
import Test.QuickCheck.Gen (unGen, generate)
import Test.QuickCheck.Random (mkQCGen)

import Random.Arbitrary (genLinMapC)
import TensorNetwork.Categorical ((⊗^), fuseBond)
import TensorNetwork.MPS.Fixed (genMPSC)
import TensorNetwork.MPS.General
  ( FullNorm, hermitianNorm, siteDagger, effectiveHBulk, effectiveHBulkInner
  , leftMPOEnv, rightMPOEnv, mpsInner, mpsMPOInner, opWire
  , mixedCanonicalCentre3
  , mpsLeft, mpsBulk, mpsRight, mpoLeft, mpoBulk, mpoRight
  )
import TensorNetwork.DMRG.Env (leftEnvBeforeBulk, rightEnvAfterBulk)
import TensorNetwork.DMRG.Fixed (tfimMPO, heffBulk)

type Bulk χ p = (C χ ⊗ C p) +> C χ

genBulk :: forall χ p. (KnownNat χ, KnownNat p, KnownNat (χ * p)) => IO (Bulk χ p)
genBulk = do
  flat <- generate (genLinMapC @(χ * p) @χ)
  pure (flat . fuseBond @χ @p)

approxEq :: Complex Double -> Complex Double -> Bool
approxEq a b = magnitude (a - b) <= 1e-8 * (1 + magnitude a + magnitude b)

report :: String -> Complex Double -> Complex Double -> IO Bool
report label lhs rhs = do
  let ok = approxEq lhs rhs
  putStrLn (if ok then "OK  " else "FAIL")
  putStrLn ("  " ++ label)
  putStrLn ("  lhs = " ++ show lhs)
  putStrLn ("  rhs = " ++ show rhs)
  putStrLn ("  |Δ| = " ++ show (magnitude (lhs - rhs)))
  pure ok

runLadder :: String -> Bool -> IO Bool
runLadder title gauge = do
  putStrLn ("== " ++ title ++ " ==")
  let psi0 = unGen (genMPSC @3 @2 @1) (mkQCGen 7) 30
      psi = if gauge then mixedCanonicalCentre3 psi0 else psi0
      mpo = tfimMPO @1 1 0.7
      nb = hermitianNorm :: FullNorm (C 3)
      np = hermitianNorm :: FullNorm (C 2)
      lEnv = leftEnvBeforeBulk nb np 0 psi mpo
      rEnv = rightEnvAfterBulk nb np 0 psi mpo
      lDirect = leftMPOEnv nb np (psi ^. mpsLeft) (mpo ^. mpoLeft) (psi ^. mpsLeft)
      rDirect = rightMPOEnv nb np (psi ^. mpsRight) (mpo ^. mpoRight) (psi ^. mpsRight)
      op = mpo ^. mpoBulk . _1
      dl = lEnv ^-^ lDirect
      dr = rEnv ^-^ rDirect
  putStrLn ("  ||L_env − L_direct||² = " ++ show (dl <.> dl :: Complex Double))
  putStrLn ("  ||R_env − R_direct||² = " ++ show (dr <.> dr :: Complex Double))

  y <- genBulk @3 @2
  x <- genBulk @3 @2
  let heffX = effectiveHBulk lEnv op rEnv x
      hs = y <.> heffX :: Complex Double
      trClose = trace $ heffX . siteDagger nb np nb y
      netFixed = effectiveHBulkInner nb np psi mpo y x
      heffMap = heffBulk nb np 0 psi mpo
      hsDriver = y <.> (heffMap $ x) :: Complex Double
      mid = opWire op x . (lEnv ⊗^ Cat.id) . siteDagger nb np nb y
      trViaR = trace $ rEnv . mid
      c = psi ^. mpsBulk . _1
      eNet = effectiveHBulkInner nb np psi mpo c c
      eHS = c <.> (effectiveHBulk lEnv op rEnv c) :: Complex Double
      eTr = trace $ effectiveHBulk lEnv op rEnv c . siteDagger nb np nb c
      z = mpsInner nb np psi psi
      eRef = mpsMPOInner nb np psi mpo psi

  ok2 <- report "step2: y<.>Heff x vs trace(Heff x ∘ siteDagger y)" hs trClose
  ok3a <- report "step3a: trace(Heff∘†) vs effectiveHBulkInner" trClose netFixed
  ok3b <- report "step3b: trace(R∘mid) vs effectiveHBulkInner" trViaR netFixed
  okDrv <- report "driver: y<.>heffBulk x vs y<.>effectiveHBulk x" hsDriver hs
  okDiagN <- report "diag network vs mpsMPOInner" eNet eRef
  okDiagHS <- report "diag: c<.>Heff c vs network" eHS eNet
  okDiagTr <- report "diag: trace(Heff c ∘ †c) vs network" eTr eNet

  putStrLn ("  mpsInner = " ++ show z)
  putStrLn ("  Rayleigh (network/‖ψ‖²) = " ++ show (realPart eRef / realPart z))
  pure (and [ok2, ok3a, ok3b, okDrv, okDiagN, okDiagHS, okDiagTr])

main :: IO ()
main = do
  ok0 <- runLadder "ungauged (seed 7)" False
  putStrLn ""
  okG <- runLadder "mixed-canonical (seed 7)" True
  putStrLn ""
  if ok0 && okG
    then putStrLn "ALL OK"
    else do
      putStrLn "FAILURES ABOVE"
      ioError (userError "heff HS vs network ladder failed")
