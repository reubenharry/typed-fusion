{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Step 1: is 'siteDagger' the Hilbert–Schmidt adjoint on bulk sites?
--
-- For maps @y,z : (χ⊗p) → χ@ we need
--
--   y <.> z  ==  trace (z ∘ siteDagger y)
--
-- Also check the flattened path (what 'siteDagger' is defined via) and
-- ordinary 'dagger' on square @C n → C n@.
--
--   cabal run site-dagger-hs-adjoint
import Prelude hiding (($), (.))
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($))
import Data.Complex (Complex, magnitude)
import Data.Proxy (Proxy (..))
import Data.VectorSpace (InnerSpace ((<.>)))
import GHC.TypeLits (KnownNat, natVal, type (*))
import Math.LinearMap.Category (type (+>), type (⊗), trace)
import Numeric.LinearAlgebra.Static (C)
import Test.QuickCheck (Gen, generate)

import Random.Arbitrary (genLinMapC)
import TensorNetwork.Categorical (fuseBond, splitBond)
import TensorNetwork.MPS.General
  ( FullNorm, hermitianNorm, siteDagger, dagger )

type Bulk χ p = (C χ ⊗ C p) +> C χ

genBulk :: forall χ p. (KnownNat χ, KnownNat p, KnownNat (χ * p)) => Gen (Bulk χ p)
genBulk = do
  flat <- genLinMapC @(χ * p) @χ
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

nat :: forall n. KnownNat n => Integer
nat = natVal (Proxy @n)

-- | Square endomorphism: @f <.> g@ vs @trace (g ∘ dagger f)@.
checkSquare :: IO Bool
checkSquare = do
  f <- generate (genLinMapC @4 @4)
  g <- generate (genLinMapC @4 @4)
  let n = hermitianNorm :: FullNorm (C 4)
      lhs = f <.> g
      rhs = trace $ g . dagger n n f
  report "square C4: f<.>g vs trace(g ∘ dagger f)" lhs rhs

-- | Flattened bulk: @yf = y∘splitBond :: C(χp)→χ@, ordinary dagger on flat.
checkFlatBulk :: forall χ p. (KnownNat χ, KnownNat p, KnownNat (χ * p)) => IO Bool
checkFlatBulk = do
  y <- generate (genBulk @χ @p)
  z <- generate (genBulk @χ @p)
  let yf = y . splitBond @χ @p
      zf = z . splitBond @χ @p
      nCod = hermitianNorm :: FullNorm (C χ)
      nDom = hermitianNorm :: FullNorm (C (χ * p))
      lhs = yf <.> zf
      rhs = trace $ zf . dagger nCod nDom yf
      lhsBulk = y <.> z
  ok1 <- report
    ("flat bulk χ=" ++ show (nat @χ) ++ " p=" ++ show (nat @p)
      ++ ": yf<.>zf vs trace(zf ∘ dagger yf)")
    lhs rhs
  ok2 <- report
    ("bulk vs flat HS: y<.>z vs yf<.>zf")
    lhsBulk lhs
  pure (ok1 && ok2)

-- | The identity DMRG needs: @y <.> z@ vs @trace (z ∘ siteDagger y)@.
checkSiteDagger :: forall χ p. (KnownNat χ, KnownNat p, KnownNat (χ * p)) => IO Bool
checkSiteDagger = do
  y <- generate (genBulk @χ @p)
  z <- generate (genBulk @χ @p)
  let nb = hermitianNorm :: FullNorm (C χ)
      np = hermitianNorm :: FullNorm (C p)
      lhs = y <.> z
      rhs = trace $ z . siteDagger nb np nb y
      rhsAlt = trace $ siteDagger nb np nb y . z
  ok1 <- report
    ("siteDagger χ=" ++ show (nat @χ) ++ " p=" ++ show (nat @p)
      ++ ": y<.>z vs trace(z ∘ siteDagger y)")
    lhs rhs
  ok2 <- report
    ("siteDagger (alt): y<.>z vs trace(siteDagger y ∘ z)")
    lhs rhsAlt
  pure (ok1 && ok2)

main :: IO ()
main = do
  putStrLn "== Step 1a: square dagger is HS adjoint =="
  okSq <- checkSquare

  putStrLn ""
  putStrLn "== Step 1b: flattened bulk dagger =="
  okFlat22 <- checkFlatBulk @2 @2
  okFlat32 <- checkFlatBulk @3 @2

  putStrLn ""
  putStrLn "== Step 1c: siteDagger vs HS on bulk sites =="
  okSD22 <- checkSiteDagger @2 @2
  okSD32 <- checkSiteDagger @3 @2

  putStrLn ""
  putStrLn "== Step 1c extras (5 more trials @ χ=3,p=2) =="
  extras <- mapM (\_ -> checkSiteDagger @3 @2) [1 .. 5 :: Int]

  let ok = and ([okSq, okFlat22, okFlat32, okSD22, okSD32] ++ extras)
  putStrLn ""
  if ok
    then putStrLn "ALL OK"
    else do
      putStrLn "FAILURES ABOVE"
      ioError (userError "siteDagger / HS adjoint check failed")
