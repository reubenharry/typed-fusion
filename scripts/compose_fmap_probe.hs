{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}

import Prelude hiding (($), (.), fmap)
import Control.Category.Constrained ((.))
import Control.Functor.Constrained (Functor (fmap))
import Control.Arrow.Constrained (($), arr)
import Data.Complex (Complex ((:+)))
import Numeric.LinearAlgebra.Static (C, M, extract, Sized (fromList))
import Math.LinearMap.Category
  ( type (+>), type (-+>), type (⊗), (⊗), LinearMap (LinearMap)
  , (-+$>), LinearSpace (applyLinear), LinearFunction (..)
  , getLinearMap
  )
import Math.LinearMap.Coercion (curryLinearMap, uncurryLinearMap, (-+$=>))
import Numeric.LinearAlgebra.Static.COrphans ()
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()

e0, e1 :: C 2
e0 = fromList [1, 0]
e1 = fromList [0, 1]

k :: (C 2 ⊗ C 2) +> C 2
k = LinearMap (fromList [1, 2, 3, 4, 5, 6, 7, 8] :: M 4 2)

g :: C 2 +> C 2
g = LinearMap (fromList [0, 1 :+ 1, 1, 0] :: M 2 2)

showM (LinearMap m) = show (extract m)

main :: IO ()
main = do
  let ck = curryLinearMap -+$=> k :: C 2 +> (C 2 +> C 2)
      h0 = ck $ e0
      -- inner fmap: LinearFunction (v+>w) (v+>w)
      postG = fmap (applyLinear -+$> g) :: (C 2 +> C 2) -+> (C 2 +> C 2)
      h0' = postG -+$> h0
  putStrLn $ "g . h0 matrix     = " ++ showM (g . h0)
  putStrLn $ "fmap postG h0 mat = " ++ showM h0'
  putStrLn $ "equal? " ++ show (showM (g . h0) == showM h0')
  putStrLn ""
  -- outer fmap over curry
  let postGOuter = fmap postG :: (C 2 +> (C 2 +> C 2)) -+> (C 2 +> (C 2 +> C 2))
      ck' = postGOuter -+$> ck
      composed = uncurryLinearMap -+$=> ck'
  putStrLn $ "manual uncurry(fmap postG (curry k)) (e0⊗e0) = "
    ++ show (extract (composed $ (e0 ⊗ e0)))
  putStrLn $ "(g . k) (e0⊗e0) = " ++ show (extract ((g . k) $ (e0 ⊗ e0)))
  putStrLn $ "g (k (e0⊗e0))   = " ++ show (extract (g $ (k $ (e0 ⊗ e0))))
  -- What does outer fmap do to ck at e0?
  putStrLn $ "ck' $ e0 matrix = " ++ showM (ck' $ e0)
  putStrLn $ "(g.h0) matrix   = " ++ showM (g . h0)
