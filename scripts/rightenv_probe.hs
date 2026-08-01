{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}

import Prelude hiding (($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($))
import Control.Lens ((^.))
import Numeric.LinearAlgebra.Static (C, extract)
import qualified Numeric.LinearAlgebra as HM
import Math.LinearMap.Category (getLinearMap, type (+>), type (⊗))
import Control.Exception (evaluate, try, SomeException)

import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

import TensorNetwork.MPS.Fixed (genMPSC)
import TensorNetwork.MPS.General
import TensorNetwork.DMRG.Fixed (tfimMPO)
import TensorNetwork.Categorical ((⊗^))

tryLabel :: String -> a -> IO ()
tryLabel label x = do
  outcome <- try (evaluate x >> pure ())
  case outcome of
    Left (ex :: SomeException) -> putStrLn $ "FAIL " ++ label ++ ": " ++ show ex
    Right _ -> putStrLn $ "OK   " ++ label

main :: IO ()
main = do
  let psi = mixedCanonicalCentre3 $ unGen (genMPSC @3 @2 @1) (mkQCGen 7) 30
      mpo = tfimMPO @1 1 0.7
      nb = hermitianNorm
      np = hermitianNorm
      bra = psi ^. mpsRight :: C 3 +> C 2
      ket = psi ^. mpsRight :: C 3 +> C 2
      op = mpo ^. mpoRight :: (C 3 ⊗ C 2) +> C 2
  putStrLn $ "op  " ++ show (HM.size (extract (getLinearMap op)))

  let idKet = (Cat.id :: C 3 +> C 3) ⊗^ ket :: (C 3 ⊗ C 3) +> (C 3 ⊗ C 2)
  tryLabel "force id⊗^ket" (getLinearMap idKet)

  let mid = op . idKet :: (C 3 ⊗ C 3) +> C 2
  tryLabel "force op.(id⊗^ket)" (getLinearMap mid)

  let r = rightMPOEnv nb np bra op ket :: (C 3 ⊗ C 3) +> C 3
  tryLabel "force rightMPOEnv" (getLinearMap r)

  tryLabel "mpsMPOInner" (mpsMPOInner nb np psi mpo psi)
