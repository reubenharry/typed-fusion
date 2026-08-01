{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExplicitNamespaces #-}

import Prelude hiding (($), (.))
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($))
import Data.Complex (Complex ((:+)))
import Numeric.LinearAlgebra.Static (C, M, Sized (fromList, extract))
import qualified Numeric.LinearAlgebra as HM
import Math.LinearMap.Category
  ( type (+>), type (⊗), (⊗), LinearMap (LinearMap), getLinearMap
  )
import Numeric.LinearAlgebra.Static.COrphans ()
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()

e0 :: C 2
e0 = fromList [1, 0]

main :: IO ()
main = do
  let k = LinearMap (fromList [1, 2, 3, 4, 5, 6, 7, 8] :: M 4 2) :: (C 2 ⊗ C 2) +> C 2
      g = LinearMap (fromList [0, 1 :+ 1, 1, 0] :: M 2 2) :: C 2 +> C 2
      gk = g . k
  putStrLn $ "g matrix:\n" ++ show (extract (getLinearMap g))
  putStrLn $ "k matrix:\n" ++ show (extract (getLinearMap k))
  putStrLn $ "g.k matrix:\n" ++ show (extract (getLinearMap gk))
  -- expected: apply g to each o-row block's columns... 
  -- nested col i is length 4 = two C2 images stacked for u-basis?
  let gEx = extract (getLinearMap g)
      kEx = extract (getLinearMap k)
      -- For each column of k (length 4), split into two C2, apply g to each? 
      -- OR treat as (m*o)×n where column is flatten of (u+>w) = M o m column-stacked
      -- u+>w as M 2 2, flatten column-major of [[a,b],[c,d]] = [a,c,b,d] or row [a,b,c,d]
      expectCol col =
        let v0 = HM.subVector 0 2 col
            v1 = HM.subVector 2 2 col
            w0 = gEx HM.#> v0
            w1 = gEx HM.#> v1
        in HM.vjoin [w0, w1]
      kcols = HM.toColumns kEx
      expect = HM.fromColumns (map expectCol kcols)
  putStrLn $ "expected g.k (g on each u-slice):\n" ++ show expect
  -- alternative: g on matvec form then convert back
  let blocks = [ HM.subMatrix (s * 2, 0) (2, 2) kEx | s <- [0,1] ]
      w = HM.fromBlocks [blocks]
      gw = gEx HM.<> w
  putStrLn $ "g <> W:\n" ++ show gw
