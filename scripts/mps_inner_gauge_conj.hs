{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Probe gauge dependence of 'mpsInner' / 'dagger' under polar absorption.
--
--   cabal run mps-inner-gauge-conj
import Prelude hiding (($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($))
import Control.Lens ((^.), (&), (.~), _1)
import Data.Complex (Complex, magnitude)
import Data.VectorSpace (InnerSpace ((<.>)))
import Numeric.LinearAlgebra.Static (C)
import Math.LinearMap.Category (type (+>), type (⊗), trace)

import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

import TensorNetwork.Categorical ((⊗^))
import TensorNetwork.MPS.Fixed (genMPSC)
import TensorNetwork.MPS.General
  ( MPS (..), FullNorm, hermitianNorm, mpsInner, toPhysicalMPS
  , dagger, siteDagger, transferLeftSite, transferBulkSite, transferRightSite
  , polarLeftSite, polarRightSite, mixedCanonicalCentre3, tensorNorm
  , mpsLeft, mpsBulk, mpsRight
  )

approx :: Complex Double -> Complex Double -> Double
approx a b = magnitude (a - b)

report :: String -> Complex Double -> IO ()
report lab z = putStrLn (lab ++ " = " ++ show z)

tr :: (C 3 +> C 3) -> Complex Double
tr m = trace $ m

main :: IO ()
main = do
  let psi0 = unGen (genMPSC @3 @2 @1) (mkQCGen 7) 30
      psiG = mixedCanonicalCentre3 psi0
      nBond = hermitianNorm :: FullNorm (C 3)
      nPhys = hermitianNorm :: FullNorm (C 2)
      oracle p = let v = toPhysicalMPS nPhys p in v <.> v
      fast p = mpsInner nBond nPhys p p

  putStrLn "=== oracle vs transfer (self-norm) ==="
  report "oracle0" (oracle psi0)
  report "fast0  " (fast psi0)
  report "oracleG" (oracle psiG)
  report "fastG  " (fast psiG)
  putStrLn ("|fast0−oracle0| = " ++ show (approx (fast psi0) (oracle psi0)))
  putStrLn ("|fastG−oracleG| = " ++ show (approx (fast psiG) (oracle psiG)))
  putStrLn ("|fastG−fast0|   = " ++ show (approx (fast psiG) (fast psi0)))

  let l0 = psi0 ^. mpsLeft
      b0 = psi0 ^. mpsBulk . _1
      r0 = psi0 ^. mpsRight
      (mL, lIso) = polarLeftSite l0
      (rIso, mR) = polarRightSite r0
      psiL = MPS lIso ((psi0 ^. mpsBulk) & _1 .~ (b0 . (mL ⊗^ Cat.id))) r0
      psiR = MPS l0   ((psi0 ^. mpsBulk) & _1 .~ (mR . b0))              rIso

  putStrLn ""
  putStrLn "=== stepwise polar absorb (oracle should stay; fast may move) ==="
  putStrLn ("|oracle(L)−oracle0| = " ++ show (approx (oracle psiL) (oracle psi0)))
  putStrLn ("|oracle(R)−oracle0| = " ++ show (approx (oracle psiR) (oracle psi0)))
  putStrLn ("|fast(L)−oracle(L)| = " ++ show (approx (fast psiL) (oracle psiL)))
  putStrLn ("|fast(R)−oracle(R)| = " ++ show (approx (fast psiR) (oracle psiR)))
  putStrLn ("|fast(L)−fast0|     = " ++ show (approx (fast psiL) (fast psi0)))
  putStrLn ("|fast(R)−fast0|     = " ++ show (approx (fast psiR) (fast psi0)))

  let tFull = transferLeftSite nBond nPhys l0 l0
      tIso  = transferLeftSite nBond nPhys lIso lIso
      mLdag = dagger nBond nBond mL
      tRecon = mL . tIso . mLdag
  putStrLn ""
  putStrLn "=== left: t(mL∘lIso) vs mL ∘ t(lIso) ∘ dagger(mL) ==="
  putStrLn ("|Tr tFull − Tr tRecon| = " ++ show (approx (tr tFull) (tr tRecon)))

  let leftBulk0 = transferBulkSite nBond nPhys b0 b0 tFull
      bNew = b0 . (mL ⊗^ Cat.id)
      leftBulk1 = transferBulkSite nBond nPhys bNew bNew tIso
  putStrLn ""
  putStrLn "=== left absorb: (left∘bulk) transfer invariance ==="
  putStrLn ("|Tr leftBulk0 − Tr leftBulk1| = "
            ++ show (approx (tr leftBulk0) (tr leftBulk1)))

  let nBondPhys = tensorNorm nBond nPhys
      mLten = mL ⊗^ Cat.id :: (C 3 ⊗ C 2) +> (C 3 ⊗ C 2)
      dagMLTen = dagger nBondPhys nBondPhys mLten
      dagMLtenFactor = mLdag ⊗^ Cat.id
      sd0 = siteDagger nBond nPhys nBond b0
      viaTen = b0 . dagMLTen . sd0
      viaFac = b0 . dagMLtenFactor . sd0
  putStrLn ""
  putStrLn "=== dagger(mL ⊗ id) vs dagger(mL) ⊗ id ==="
  putStrLn ("|Tr(b0∘dagger(mL⊗id)∘sd0) − Tr(b0∘(mL†⊗id)∘sd0)| = "
            ++ show (approx (tr viaTen) (tr viaFac)))

  let sd1 = siteDagger nBond nPhys nBond bNew
      sdRecon = dagMLtenFactor . sd0
      thru1 = bNew . sd1
      thruR = bNew . sdRecon
  putStrLn ""
  putStrLn "=== siteDagger(b∘(mL⊗id)) vs (mL†⊗id)∘siteDagger(b) ==="
  putStrLn ("|Tr(bNew∘sd1) − Tr(bNew∘(mL†⊗id)∘sd0)| = "
            ++ show (approx (tr thru1) (tr thruR)))

  let env = leftBulk0
      closeCode = transferRightSite nBond nPhys r0 r0 env
      closeAlt  = trace $ (env . dagger nPhys nBond r0 . r0)
  putStrLn ""
  putStrLn "=== right close dagger(ket).bra vs dagger(bra).ket (bra=ket) ==="
  report "code" closeCode
  report "alt " closeAlt
  putStrLn ("|diff| = " ++ show (approx closeCode closeAlt))
