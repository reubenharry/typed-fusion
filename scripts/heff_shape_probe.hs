{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}

-- | What shape is LinearMap storage for TFIM Heff pieces?
import Prelude hiding (($), (.))
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($))
import Control.Lens ((^.), _1)
import Numeric.LinearAlgebra.Static (C, extract)
import qualified Numeric.LinearAlgebra as HM
import Math.LinearMap.Category (getLinearMap, type (+>), type (⊗), LinearMap)

import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

import TensorNetwork.MPS.Fixed (genMPSC)
import TensorNetwork.MPS.General
import TensorNetwork.DMRG.Fixed (tfimMPO, heffBulk)
import Control.Exception (evaluate, try, SomeException)

main :: IO ()
main = do
  let psi0 = unGen (genMPSC @3 @2 @1) (mkQCGen 7) 30
      psiG = mixedCanonicalCentre3 psi0
      mpo = tfimMPO @1 1 0.7
      nb = hermitianNorm
      np = hermitianNorm
      centre = psiG ^. mpsBulk . _1
  putStrLn $ "centre storage " ++ show (HM.size (extract (getLinearMap centre)))
  let l = leftMPOEnv nb np (psiG ^. mpsLeft) (mpo ^. mpoLeft) (psiG ^. mpsLeft)
      r = rightMPOEnv nb np (psiG ^. mpsRight) (mpo ^. mpoRight) (psiG ^. mpsRight)
      op = mpo ^. mpoBulk . _1
  putStrLn $ "leftEnv storage  " ++ show (HM.size (extract (getLinearMap l)))
  putStrLn $ "rightEnv storage " ++ show (HM.size (extract (getLinearMap r)))
  putStrLn $ "op storage       " ++ show (HM.size (extract (getLinearMap op)))
  outcome <- try (evaluate (getLinearMap (effectiveHBulk l op r centre) `seq` ()))
  case outcome of
    Left (ex :: SomeException) -> putStrLn $ "Heff apply CRASH: " ++ show ex
    Right _ -> putStrLn "Heff apply OK"
  outcome2 <- try (evaluate (heffBulk nb np 0 psiG mpo `seq` ()))
  case outcome2 of
    Left (ex :: SomeException) -> putStrLn $ "heffBulk CRASH: " ++ show ex
    Right _ -> putStrLn "heffBulk OK"
