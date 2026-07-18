{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
import Prelude hiding (($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($))
import Math.LinearMap.Category (trace)
import Data.VectorSpace (InnerSpace ((<.>)))
import TensorNetwork.Categorical ((⊗^))
import TensorNetwork.MPS.Fixed
import TensorNetwork.MPS.General

import Test.QuickCheck (generate)
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)
import TensorNetwork.MPS.Fixed (genMPSC, exampleMPO)

main :: IO ()
main = do
  let mpsEnv = unGen (genMPSC @2 @2 @1) (mkQCGen 0) 30
      mpsKet = unGen (genMPSC @2 @2 @1) (mkQCGen 1) 30
  let mps = mpsEnv
      mpo = exampleMPO
      y = bulkSite1 (mpsBulk mpsEnv)
      x = bulkSite1 (mpsBulk mpsKet)
      nb = hermitianNorm
      np = hermitianNorm
      l = leftMPOEnv nb np (mpsLeft mps) (mpoLeft mpo) (mpsLeft mps)
      r = rightMPOEnv nb np (mpsRight mps) (mpoRight mpo) (mpsRight mps)
      op = bulkSite1 (mpoBulk mpo)
      heffX = effectiveHBulk l op r x
      lhs1 = y <.> heffX
      lhs2 =
        trace $
          r . opWire op x . (l ⊗^ Cat.id) . siteDagger nb np nb y
      lhs3 =
        transferMPORightSite nb np (mpsRight mps) (mpoRight mpo) (mpsRight mps) $
          transferMPOBulkSite nb np y op x l
      rhs =
        mpsMPOInner nb np
          (mpsWithBulkSite y mpsEnv)
          mpo
          (mpsWithBulkSite x mpsEnv)
  putStrLn $ "lhs1 = " ++ show lhs1
  putStrLn $ "lhs2 = " ++ show lhs2
  putStrLn $ "lhs3 = " ++ show lhs3
  putStrLn $ "rhs  = " ++ show rhs
