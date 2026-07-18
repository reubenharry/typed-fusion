{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Isolate whether bug 2 is in curry/uncurry or only in sample/arr(id).
import Prelude hiding (($), (.))
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($))
import Data.Complex (Complex ((:+)))
import Numeric.LinearAlgebra.Static (C, M, extract, Sized (fromList))
import Math.LinearMap.Category
  ( type (+>), type (⊗), (⊗)
  , LinearMap (LinearMap)
  )
import Math.LinearMap.Coercion (curryLinearMap, uncurryLinearMap, (-+$=>))
import Numeric.LinearAlgebra.Static.COrphans ()
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()

e0, e1 :: C 2
e0 = fromList [1, 0]
e1 = fromList [0, 1]

k :: (C 2 ⊗ C 2) +> C 2
k = LinearMap (fromList [1, 2, 3, 4, 5, 6, 7, 8])

g :: C 2 +> C 2
g = LinearMap (fromList [0, 1 :+ 1, 1, 0] :: M 2 2)

main :: IO ()
main = do
  putStrLn "-- curry law: (curry k $ u) $ v  ≡  k $ (u ⊗ v) --"
  let ck = curryLinearMap -+$=> k :: C 2 +> (C 2 +> C 2)
  mapM_ (\(nu,u) -> mapM_ (\(nv,v) -> do
    let lhs = (ck $ u) $ v
        rhs = k $ (u ⊗ v)
    putStrLn $ "  u=" ++ nu ++ " v=" ++ nv
            ++ "  curry= " ++ show (extract lhs)
            ++ "  apply= " ++ show (extract rhs)
            ++ "  ok? " ++ show (extract lhs == extract rhs)
    ) [("e0",e0),("e1",e1)]) [("e0",e0),("e1",e1)]

  putStrLn ""
  putStrLn "-- uncurry . curry = id on application --"
  let k' = uncurryLinearMap -+$=> ck
  mapM_ (\(nm,t) -> putStrLn $ "  " ++ nm
          ++ "  k= " ++ show (extract (k $ t))
          ++ "  (u.c)k= " ++ show (extract (k' $ t))
          ++ "  ok? " ++ show (extract (k $ t) == extract (k' $ t)))
    [("e0⊗e0", e0⊗e0), ("e0⊗e1", e0⊗e1), ("e1⊗e0", e1⊗e0), ("e1⊗e1", e1⊗e1)]

  putStrLn ""
  putStrLn "-- category compose (g . k) vs g (k t) --"
  mapM_ (\(nm,t) -> putStrLn $ "  " ++ nm
          ++ "  (g.k)= " ++ show (extract ((g . k) $ t))
          ++ "  g(k t)= " ++ show (extract (g $ (k $ t)))
          ++ "  ok? " ++ show (extract ((g . k) $ t) == extract (g $ (k $ t))))
    [("e0⊗e0", e0⊗e0), ("e0⊗e1", e0⊗e1), ("e1⊗e0", e1⊗e0), ("e1⊗e1", e1⊗e1)]
