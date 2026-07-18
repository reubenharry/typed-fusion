{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Where does the conjugate appear in (g . k)?
import Prelude hiding (($), (.), fmap)
import Control.Category.Constrained ((.))
import Control.Functor.Constrained (Functor (fmap))
import Control.Arrow.Constrained (($))
import Data.Complex (Complex ((:+)), conjugate)
import Numeric.LinearAlgebra.Static (C, M, extract, Sized (fromList))
import Math.LinearMap.Category
  ( type (+>), type (⊗), (⊗), LinearMap (LinearMap)
  , (-+$>), LinearSpace (applyLinear), LinearFunction (..)
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
      h0 = ck $ e0  -- C2 +> C2
  putStrLn $ "h0 = curry k $ e0, matrix = " ++ show (extract (case h0 of LinearMap m -> m))
  putStrLn $ "h0 $ e0 = " ++ show (extract (h0 $ e0))
  putStrLn $ "g $ (h0 $ e0) = " ++ show (extract (g $ (h0 $ e0)))
  putStrLn $ "(g . h0) $ e0 = " ++ show (extract ((g . h0) $ e0))
  putStrLn $ "plain postcompose ok? "
    ++ show (extract (g $ (h0 $ e0)) == extract ((g . h0) $ e0))
  -- category (g . k)
  putStrLn $ "(g . k) (e0⊗e0) = " ++ show (extract ((g . k) $ (e0 ⊗ e0)))
  putStrLn $ "g (k (e0⊗e0))   = " ++ show (extract (g $ (k $ (e0 ⊗ e0))))
