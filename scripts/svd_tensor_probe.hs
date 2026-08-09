{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

import Prelude hiding (($), (.))
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($))
import Data.Complex (realPart)
import Data.Functor.Identity (runIdentity)
import Data.List (sortOn)
import Data.Ord (Down (..))
import Data.VectorSpace (magnitudeSq, (^-^))
import Math.LinearMap.Category (FiniteDimensional (..))
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.VectorSpace.Initializable
import Numeric.LinearAlgebra.Static (C)
import Numeric.LinearAlgebra.Static.COrphans ()
import System.Random (mkStdGen)
import Experiments.SVD

main :: IO ()
main = do
  let flat = randomMapC @4 @3 (mkStdGen 44)
      aFun = asLinearFunction flat
      seeds = enumerateSubBasis (entireBasis :: SubBasis (C 4))
      ps = runIdentity (svdC (FixedInitialVectors seeds) aFun 3)
      ranked = sortOn (Down . realPart . singularValue) ps
  putStrLn $ "all sis = " ++ show (singularValue <$> ranked)
  let ranked3 = take 3 ranked
      rebuilt = reconstructFromPendants @(C 3) ranked3
      errs =
        [ sqrt (realPart (magnitudeSq ((aFun $ e) ^-^ (rebuilt $ e))))
        | e <- seeds
        ]
  putStrLn $ "per-basis errs = " ++ show errs
  putStrLn $ "max err = " ++ show (maximum errs)

  -- Also try chi = C 3 via svdFactorsC (same thing)
  let (vt, s, u) = svdFactorsC @(C 3) aFun
      rebuilt2 = u . s . vt
      err2 =
        maximum
          [ sqrt (realPart (magnitudeSq ((aFun $ e) ^-^ (rebuilt2 $ e))))
          | e <- seeds
          ]
  putStrLn $ "svdFactorsC err = " ++ show err2
