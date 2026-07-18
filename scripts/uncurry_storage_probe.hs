{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}

import Prelude hiding (($), (.), fmap)
import Control.Category.Constrained ((.))
import Control.Functor.Constrained (Functor (fmap))
import Control.Arrow.Constrained (($))
import Data.Complex (Complex ((:+)))
import Numeric.LinearAlgebra.Static (C, M, extract, Sized (fromList))
import qualified Numeric.LinearAlgebra as HM
import Math.LinearMap.Category
  ( type (+>), type (-+>), type (⊗), (⊗), LinearMap (LinearMap)
  , (-+$>), LinearSpace (applyLinear), LinearFunction (..), getLinearMap
  )
import Math.LinearMap.Coercion (curryLinearMap, uncurryLinearMap, (-+$=>))
import Numeric.LinearAlgebra.Static.COrphans ()
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()

e0 :: C 2
e0 = fromList [1, 0]

k :: (C 2 ⊗ C 2) +> C 2
k = LinearMap (fromList [1, 2, 3, 4, 5, 6, 7, 8] :: M 4 2)

g :: C 2 +> C 2
g = LinearMap (fromList [0, 1 :+ 1, 1, 0] :: M 2 2)

main :: IO ()
main = do
  let ck = curryLinearMap -+$=> k :: C 2 +> (C 2 +> C 2)
      postG = fmap (applyLinear -+$> g) :: (C 2 +> C 2) -+> (C 2 +> C 2)
      ck' = fmap postG -+$> ck
      composed = uncurryLinearMap -+$=> ck'
  putStrLn "-- raw storage of ck' (should be M 4 2) --"
  putStrLn $ show (extract (getLinearMap ck'))
  putStrLn "-- raw storage of uncurry ck' --"
  putStrLn $ show (extract (getLinearMap composed))
  putStrLn "-- same bytes? --"
  putStrLn $ show (extract (getLinearMap ck') == extract (getLinearMap composed))
  putStrLn "-- (ck' $ e0) matrix --"
  putStrLn $ show (extract (getLinearMap (ck' $ e0)))
  putStrLn "-- col0 of ck' storage --"
  putStrLn $ show (HM.toList (extract (getLinearMap ck') HM.! 0))
  -- compare g(k t) vs composed
  putStrLn $ "g(k(e0⊗e0))     = " ++ show (extract (g $ (k $ (e0 ⊗ e0))))
  putStrLn $ "composed(e0⊗e0) = " ++ show (extract (composed $ (e0 ⊗ e0)))
  putStrLn $ "(ck'$e0)$e0     = " ++ show (extract ((ck' $ e0) $ e0))
