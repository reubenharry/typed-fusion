{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Pin why densified RightMPOEnv breaks Heff HS pairing.
--
--   cabal run heff-compose-bug
import Prelude hiding (($), (.))
import Control.Category.Constrained ((.))
import qualified Control.Category.Constrained as Cat
import Control.Arrow.Constrained (($), arr)
import Control.Lens ((^.), _1)
import Data.Complex (Complex, magnitude)
import Data.VectorSpace (InnerSpace ((<.>)), Scalar, sumV)
import Math.LinearMap.Category
  ( type (+>), type (⊗), LinearFunction (..), pattern LinearFunction
  , FiniteDimensional (..), trace
  )
import Numeric.LinearAlgebra.Static (C)
import Test.QuickCheck (generate)
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

import Random.Arbitrary (genLinMapC)
import TensorNetwork.Categorical ((⊗^), fuseBond, splitBond)
import TensorNetwork.MPS.Fixed (genMPSC)
import TensorNetwork.MPS.General
import TensorNetwork.DMRG.Fixed (tfimMPO)
import TensorNetwork.DMRG.Env (leftEnvBeforeBulk, rightEnvAfterBulk)

-- | Frobenius via applies on the fused @C 6@ ONB (no Category compose of Heff).
frobeniusFlat
  :: (C 3 ⊗ C 2) +> C 3
  -> (C 3 ⊗ C 2) +> C 3
  -> Complex Double
frobeniusFlat a b =
  let es = [ splitBond @3 @2 $ e | e <- enumerateSubBasis (entireBasis @(C 6)) ]
  in sumV [ (a $ e) <.> (b $ e) | e <- es ]

approx :: Complex Double -> Complex Double -> Bool
approx a b = magnitude (a - b) <= 1e-8 * (1 + magnitude a + magnitude b)

report :: String -> Complex Double -> Complex Double -> IO Bool
report lab lhs rhs = do
  let ok = approx lhs rhs
  putStrLn (if ok then "OK  " else "FAIL")
  putStrLn ("  " ++ lab)
  putStrLn ("  lhs = " ++ show lhs)
  putStrLn ("  rhs = " ++ show rhs)
  putStrLn ("  |Δ| = " ++ show (magnitude (lhs - rhs)))
  pure ok

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
      opB = mpo ^. mpoBulk . _1
      middle x = opWire opB x . (l ⊗^ Cat.id)
      heffStored x = r . middle x
      heffApply x =
        arr (LinearFunction (\xp -> r $ (middle x $ xp)))
      heffExpand x =
        dagger np nb rr . ro . (Cat.id ⊗^ rr) . middle x
      inner = effectiveHBulkInner nb np psi mpo y y
      mid = middle y . siteDagger nb np nb y

  putStrLn "== scalars =="
  putStrLn ("Inner                 = " ++ show inner)
  putStrLn ("transfer(mid)         = " ++ show (transferMPORightSite nb np rr ro rr mid))
  putStrLn ("trace (full ∘ mid)    = " ++ show (trace $ dagger np nb rr . ro . (Cat.id ⊗^ rr) . mid :: Complex Double))
  putStrLn ("trace (R ∘ mid)       = " ++ show (trace $ r . mid :: Complex Double))

  putStrLn ""
  putStrLn "== HS <.> vs apply-Frobenius on Heff =="
  _ <- report "HS stored vs Inner" (y <.> heffStored y) inner
  _ <- report "HS apply vs Inner" (y <.> heffApply y) inner
  _ <- report "FrobApply stored vs Inner" (frobeniusFlat y (heffStored y)) inner
  _ <- report "FrobApply apply vs Inner" (frobeniusFlat y (heffApply y)) inner
  _ <- report "FrobApply expand vs Inner" (frobeniusFlat y (heffExpand y)) inner

  putStrLn ""
  putStrLn "== control: flat-built bulk, <.> vs FrobApply =="
  flat <- generate (genLinMapC @6 @3)
  let z = flat . fuseBond @3 @2
  okCtrl <- report "y<.>z vs FrobApply y z" (y <.> z) (frobeniusFlat y z)

  putStrLn ""
  if okCtrl
    then putStrLn "control OK (flat bulk HS = apply Frobenius)"
    else putStrLn "control FAIL"
  putStrLn "Done."
