{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Follow-up: is Heff wrong pointwise, or only Trace(Heff∘†)?
--
--   cabal run heff-compose-bug2
import Prelude hiding (($), (.))
import Control.Category.Constrained ((.))
import qualified Control.Category.Constrained as Cat
import Control.Arrow.Constrained (($), arr)
import Control.Lens ((^.), _1)
import Data.Complex (Complex, magnitude)
import Data.VectorSpace (InnerSpace ((<.>)), sumV, (^-^))
import Math.LinearMap.Category
  ( type (+>), type (⊗), LinearFunction (..), pattern LinearFunction
  , FiniteDimensional (..), trace
  )
import Numeric.LinearAlgebra.Static (C)
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

import TensorNetwork.Categorical ((⊗^), splitBond)
import TensorNetwork.MPS.Fixed (genMPSC)
import TensorNetwork.MPS.General
import TensorNetwork.DMRG.Fixed (tfimMPO)
import TensorNetwork.DMRG.Env (leftEnvBeforeBulk, rightEnvAfterBulk)

domainBasis :: [C 3 ⊗ C 2]
domainBasis = [ splitBond @3 @2 $ e | e <- enumerateSubBasis (entireBasis @(C 6)) ]

frobeniusFlat a b =
  sumV [ (a $ e) <.> (b $ e) | e <- domainBasis ]

d2 v = v <.> v :: Complex Double

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
      middle = opWire opB y . (l ⊗^ Cat.id)
      -- three Heff constructions
      heffStored = r . middle
      heffApply = arr (LinearFunction (\xp -> r $ (middle $ xp)))
      heffExpand = dagger np nb rr . ro . (Cat.id ⊗^ rr) . middle
      -- pointwise expand apply (no Category on R)
      applyExpand xp =
        dagger np nb rr $ (ro $ ((Cat.id ⊗^ rr) $ (middle $ xp)))
      dagY = siteDagger nb np nb y
      mid = middle . dagY
      inner = effectiveHBulkInner nb np psi mpo y y

  putStrLn "== pointwise: Heff e vs expand-apply e =="
  let diffs =
        [ d2 ((heffExpand $ e) ^-^ applyExpand e)
        | e <- domainBasis
        ]
  putStrLn ("max ||HeffExpand e - applyExpand e||^2 = " ++ show (maximum (map magnitude diffs)))
  let diffsS =
        [ d2 ((heffStored $ e) ^-^ applyExpand e)
        | e <- domainBasis
        ]
  putStrLn ("max ||HeffStored e - applyExpand e||^2 = " ++ show (maximum (map magnitude diffsS)))
  let diffsA =
        [ d2 ((heffApply $ e) ^-^ applyExpand e)
        | e <- domainBasis
        ]
  putStrLn ("max ||HeffApply e - applyExpand e||^2 = " ++ show (maximum (map magnitude diffsA)))

  putStrLn ""
  putStrLn "== Trace variants =="
  putStrLn ("Inner              = " ++ show inner)
  putStrLn ("trace full∘mid     = " ++ show (trace $ dagger np nb rr . ro . (Cat.id ⊗^ rr) . mid :: Complex Double))
  putStrLn ("trace R∘mid        = " ++ show (trace $ r . mid :: Complex Double))
  putStrLn ("trace HeffExp∘†    = " ++ show (trace $ heffExpand . dagY :: Complex Double))
  putStrLn ("trace HeffStore∘†  = " ++ show (trace $ heffStored . dagY :: Complex Double))
  putStrLn ("trace HeffApply∘†  = " ++ show (trace $ heffApply . dagY :: Complex Double))

  putStrLn ""
  putStrLn "== Frobenius =="
  putStrLn ("Frob HeffExpand    = " ++ show (frobeniusFlat y heffExpand))
  putStrLn ("Frob HeffStored    = " ++ show (frobeniusFlat y heffStored))
  -- apply-only Frobenius with pointwise expand (never builds Heff map)
  let frobPoint =
        sumV [ (y $ e) <.> applyExpand e | e <- domainBasis ]
  putStrLn ("Frob pointwise     = " ++ show frobPoint)

  putStrLn ""
  putStrLn "== Does Trace(full∘mid) equal Frob pointwise? =="
  let trFull = trace $ dagger np nb rr . ro . (Cat.id ⊗^ rr) . mid
  putStrLn ("|trFull - frobPoint| = " ++ show (magnitude (trFull - frobPoint)))
  putStrLn ("|inner - frobPoint|  = " ++ show (magnitude (inner - frobPoint)))
  putStrLn ("|inner - trFull|     = " ++ show (magnitude (inner - trFull)))
