{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
import Prelude hiding (($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($))
import Control.Lens ((^.))
import Math.LinearMap.Category (trace)
import Data.VectorSpace (InnerSpace ((<.>)))
import TensorNetwork.Categorical ((⊗^))
import TensorNetwork.MPS.Fixed
import TensorNetwork.MPS.General

import Test.QuickCheck (generate)
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)
import TensorNetwork.MPS.Fixed (genMPSC, exampleMPO)

-- main :: IO ()
-- main = do
--   let mpsEnv = unGen (genMPSC @2 @2 @1) (mkQCGen 0) 30
--       mpsKet = unGen (genMPSC @2 @2 @1) (mkQCGen 1) 30
--   let mps = mpsEnv
--       mpo = exampleMPO
--       y = bulkSite1 (mpsEnv ^. mpsBulk)
--       x = bulkSite1 (mpsKet ^. mpsBulk)
--       nb = hermitianNorm
--       np = hermitianNorm
--       l = leftMPOEnv nb np (mps ^. mpsLeft) (mpo ^. mpoLeft) (mps ^. mpsLeft)
--       r = rightMPOEnv nb np (mps ^. mpsRight) (mpo ^. mpoRight) (mps ^. mpsRight)
--       op = bulkSite1 (mpo ^. mpoBulk)
--       heffX = effectiveHBulk l op r x
--       lhs1 = y <.> heffX
--       lhs2 =
--         trace $
--           r . opWire op x . (l ⊗^ Cat.id) . siteDagger nb np nb y
--       lhs3 =
--         transferMPORightSite nb np (mps ^. mpsRight) (mpo ^. mpoRight) (mps ^. mpsRight) $
--           transferMPOBulkSite nb np y op x l
--       rhs =
--         mpsMPOInner nb np
--           (mpsWithBulkSite y mpsEnv)
--           mpo
--           (mpsWithBulkSite x mpsEnv)
--   putStrLn $ "lhs1 = " ++ show lhs1
--   putStrLn $ "lhs2 = " ++ show lhs2
--   putStrLn $ "lhs3 = " ++ show lhs3
--   putStrLn $ "rhs  = " ++ show rhs
