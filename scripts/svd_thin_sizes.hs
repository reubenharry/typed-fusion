{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

import Prelude hiding (($), (.))
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($))
import Data.Complex (realPart)
import Data.VectorSpace (magnitudeSq, (^-^))
import Math.LinearMap.Category (FiniteDimensional (..))
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static (C)
import Numeric.LinearAlgebra.Static.COrphans ()
import System.Random (mkStdGen)
import GHC.TypeLits (KnownNat)
import Experiments.SVD

go
  :: forall n m k
   . (KnownNat n, KnownNat m, KnownNat k)
  => String -> Int -> IO ()
go label seed = do
  let aFun = asLinearFunction (randomMapC @n @m (mkStdGen seed))
      (vt, s, u) = svdFactorsC @(C k) aFun
      rebuilt = u . s . vt
      es = enumerateSubBasis (entireBasis :: SubBasis (C n))
      err =
        maximum
          [ sqrt (realPart (magnitudeSq ((aFun $ e) ^-^ (rebuilt $ e))))
          | e <- es
          ]
  putStrLn $ label ++ " err=" ++ show err

main :: IO ()
main = do
  go @3 @2 @2 "C3→C2" 42
  go @4 @2 @2 "C4→C2" 45
  go @4 @3 @3 "C4→C3" 44
  go @6 @2 @2 "C6→C2" 46
  go @4 @4 @4 "C4→C4" 44
