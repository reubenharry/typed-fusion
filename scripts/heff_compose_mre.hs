{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

-- | Regression: densified 'composeLinear' must be associative on the
-- MPS–MPO @rightMPOEnv@ witness (Static×Static applyLinear path in COrphans).
--
-- With TFIM seed 7, @mixedCanonicalCentre3@, @χ=3@, @p=2@, @n=1@:
--
--   a = dagger rr,  b = ro,  c = id⊗rr,  m = mid
--   R = a ∘ b ∘ c
--
--   (R∘m)$e == (a∘b∘c∘m)$e
--   trace(R∘m) == trace(a∘b∘c∘m) == effectiveHBulkInner
--
--   cabal run heff-compose-mre
import Prelude hiding (($), (.))
import Control.Category.Constrained ((.))
import qualified Control.Category.Constrained as Cat
import Control.Arrow.Constrained (($))
import Control.Lens ((^.), _1)
import Data.Complex (Complex, magnitude)
import Data.VectorSpace (InnerSpace ((<.>)), Scalar, (^-^))
import Math.LinearMap.Category (trace, FiniteDimensional (..))
import Numeric.LinearAlgebra.Static (C)
import System.Exit (exitFailure, exitSuccess)
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

import TensorNetwork.Categorical ((⊗^))
import TensorNetwork.MPS.Fixed (genMPSC)
import TensorNetwork.MPS.General
import TensorNetwork.DMRG.Fixed (tfimMPO)
import TensorNetwork.DMRG.Env (leftEnvBeforeBulk, rightEnvAfterBulk)

d2 :: (InnerSpace v, Scalar v ~ Complex Double) => v -> Complex Double
d2 v = v <.> v

approx :: Complex Double -> Complex Double -> Bool
approx a b = magnitude (a - b) <= 1e-8 * (1 + magnitude a + magnitude b)

main :: IO ()
main = do
  let psi = mixedCanonicalCentre3 $ unGen (genMPSC @3 @2 @1) (mkQCGen 7) 30
      mpo = tfimMPO @1 1 0.7
      nb = hermitianNorm
      np = hermitianNorm
      y = psi ^. mpsBulk . _1
      l = leftEnvBeforeBulk nb np 0 psi mpo
      r = rightEnvAfterBulk nb np 0 psi mpo
      rr = psi ^. mpsRight
      ro = mpo ^. mpoRight
      a = dagger np nb rr
      b = ro
      c = Cat.id ⊗^ rr
      m =
        opWire (mpo ^. mpoBulk . _1) y
          . (l ⊗^ Cat.id)
          . siteDagger nb np nb y
      -- infixr (.): full = a . (b . (c . m))
      full = a . b . c . m
      rMid = r . m
      seqABC t = a $ (b $ (c $ t))
      basis = enumerateSubBasis (entireBasis @(C 3))
      e0 = case basis of
        (e:_) -> e
        [] -> error "empty basis"
      t0 = m $ e0
      inner = effectiveHBulkInner nb np psi mpo y y

  putStrLn "== A. R $ t == a$(b$(c$t)) =="
  let dA = d2 ((r $ t0) ^-^ seqABC t0)
      okA = magnitude dA < 1e-16
  putStrLn (if okA then "OK  " else "FAIL")
  putStrLn ("  ||R t − seq||² = " ++ show dA)

  putStrLn ""
  putStrLn "== B. (R∘m)$e == R$(m$e) =="
  let dB = maximum
        [ magnitude (d2 ((rMid $ e) ^-^ (r $ (m $ e))))
        | e <- basis
        ]
      okB = dB < 1e-16
  putStrLn (if okB then "OK  " else "FAIL")
  putStrLn ("  max ||Δ||² = " ++ show dB)

  putStrLn ""
  putStrLn "== C. (R∘m)$e == (a∘b∘c∘m)$e  [associativity] =="
  let dC = maximum
        [ magnitude (d2 ((rMid $ e) ^-^ (full $ e)))
        | e <- basis
        ]
      okC = dC < 1e-16
  putStrLn (if okC then "OK  " else "FAIL")
  putStrLn ("  max ||Δ||² = " ++ show dC)

  putStrLn ""
  putStrLn "== D. trace(R∘m) == trace(a∘b∘c∘m) =="
  let trR = trace $ rMid
      trF = trace $ full
      okD = approx trR trF
  putStrLn (if okD then "OK  " else "FAIL")
  putStrLn ("  trace(R∘m) = " ++ show (trR :: Complex Double))
  putStrLn ("  trace(full) = " ++ show (trF :: Complex Double))
  putStrLn ("  |Δ|         = " ++ show (magnitude (trR - trF)))

  putStrLn ""
  putStrLn "== E. trace(full) == effectiveHBulkInner =="
  let okE = approx trF inner
  putStrLn (if okE then "OK  " else "FAIL")
  putStrLn ("  Inner = " ++ show (inner :: Complex Double))

  putStrLn ""
  let allOk = okA && okB && okC && okD && okE
      -- Bug witness: R applies and Category-vs-apply OK, but (R∘m) ≠ full.
      bugPattern = okA && okB && not okC && not okD && okE
  if allOk
    then do
      putStrLn "ALL OK (composeLinear associative on this witness)"
      exitSuccess
    else if bugPattern
      then do
        putStrLn
          "MRE reproduced: densified (a∘b∘c)∘m ≠ a∘b∘c∘m (physics = full)."
        exitFailure
      else do
        putStrLn "Unexpected pattern:"
        putStrLn ("  A R-apply OK?     " ++ show okA)
        putStrLn ("  B Cat/apply OK?   " ++ show okB)
        putStrLn ("  C associative?    " ++ show okC)
        putStrLn ("  D Trace agree?    " ++ show okD)
        putStrLn ("  E Inner=full?     " ++ show okE)
        exitFailure
