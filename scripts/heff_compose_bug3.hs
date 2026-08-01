{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

-- | Is Trace broken, or mid≠middle∘† pointwise, or HS≠network for true Heff?
--
--   cabal run heff-compose-bug3
import Prelude hiding (($), (.))
import Control.Category.Constrained ((.))
import qualified Control.Category.Constrained as Cat
import Control.Arrow.Constrained (($))
import Control.Lens ((^.), _1)
import Data.Complex (Complex, magnitude)
import Data.VectorSpace (InnerSpace ((<.>)), sumV, (^-^))
import Math.LinearMap.Category
  ( type (+>), type (⊗), FiniteDimensional (..), trace )
import Numeric.LinearAlgebra.Static (C)
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

import TensorNetwork.Categorical ((⊗^), splitBond)
import TensorNetwork.MPS.Fixed (genMPSC)
import TensorNetwork.MPS.General
import TensorNetwork.DMRG.Fixed (tfimMPO)
import TensorNetwork.DMRG.Env (leftEnvBeforeBulk)

d2 v = v <.> v :: Complex Double

main :: IO ()
main = do
  let psi = mixedCanonicalCentre3 $ unGen (genMPSC @3 @2 @1) (mkQCGen 7) 30
      mpo = tfimMPO @1 1 0.7
      nb = hermitianNorm
      np = hermitianNorm
      y = psi ^. mpsBulk . _1
      l = leftEnvBeforeBulk nb np 0 psi mpo
      rr = psi ^. mpsRight
      ro = mpo ^. mpoRight
      opB = mpo ^. mpoBulk . _1
      middle = opWire opB y . (l ⊗^ Cat.id)
      dagY = siteDagger nb np nb y
      mid = middle . dagY
      -- χ ONB
      bs = enumerateSubBasis (entireBasis @(C 3))
      -- χ⊗p ONB via split
      es = [ splitBond @3 @2 $ e | e <- enumerateSubBasis (entireBasis @(C 6)) ]
      applyR m =
        dagger np nb rr $ (ro $ ((Cat.id ⊗^ rr) $ m))
      -- pointwise full close on χ: v ↦ R(middle(† v))
      applyClose v = applyR (middle $ (dagY $ v))
      -- Category full∘mid apply
      fullMid = dagger np nb rr . ro . (Cat.id ⊗^ rr) . mid
      trFull = trace $ fullMid
      -- Trace via diagonal applies on Category map
      trDiagCat = sumV [ b <.> (fullMid $ b) | b <- bs ]
      -- Trace via diagonal of pointwise close
      trDiagPt = sumV [ b <.> applyClose b | b <- bs ]
      -- Frob of pointwise Heff
      frob = sumV [ (y $ e) <.> applyR (middle $ e) | e <- es ]
      inner = effectiveHBulkInner nb np psi mpo y y

  putStrLn "== mid vs middle∘† pointwise on χ =="
  putStrLn ("max ||mid v - middle(†v)||^2 = "
    ++ show (maximum [ magnitude (d2 ((mid $ b) ^-^ (middle $ (dagY $ b)))) | b <- bs ]))

  putStrLn ""
  putStrLn "== fullMid vs pointwise close on χ =="
  putStrLn ("max ||fullMid v - applyClose v||^2 = "
    ++ show (maximum [ magnitude (d2 ((fullMid $ b) ^-^ applyClose b)) | b <- bs ]))

  putStrLn ""
  putStrLn "== Trace vs diagonal sums =="
  putStrLn ("Inner            = " ++ show inner)
  putStrLn ("trace fullMid    = " ++ show (trFull :: Complex Double))
  putStrLn ("diag sum Cat     = " ++ show trDiagCat)
  putStrLn ("diag sum point   = " ++ show trDiagPt)
  putStrLn ("Frob Heff point  = " ++ show frob)
  putStrLn ("|tr - diagCat|   = " ++ show (magnitude (trFull - trDiagCat)))
  putStrLn ("|tr - diagPt|    = " ++ show (magnitude (trFull - trDiagPt)))
  putStrLn ("|tr - Frob|      = " ++ show (magnitude (trFull - frob)))
  putStrLn ("|diagPt - Frob|  = " ++ show (magnitude (trDiagPt - frob)))
  putStrLn ("|inner - tr|     = " ++ show (magnitude (inner - trFull)))
  putStrLn ("|inner - Frob|   = " ++ show (magnitude (inner - frob)))
