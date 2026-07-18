{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}

-- | Minimal probe: does @f ⊗^ id@ act as @f@ on the first tensor factor,
-- and does @.@ compose correctly, for matrix-backed maps on C spaces?
import Prelude hiding (($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($), arr)
import Data.Complex (Complex ((:+)))
import Numeric.LinearAlgebra.Static (C, M, extract, Sized (fromList))
import Math.LinearMap.Category
  (getLinearMap, type (+>), type (-+>), type (⊗), (⊗), Tensor (getTensorProduct), LinearMap (LinearMap))
import qualified Numeric.LinearAlgebra as HM
import TensorNetwork.MPS.General ()
import TensorNetwork.Categorical ((⊗^))

-- f: C 2 +> C 2 with distinct entries (storage M cod dom, row-major fromList):
-- matrix [[1,2],[3,4]]  =>  f e0 = (1,3), f e1 = (2,4)
f :: C 2 +> C 2
f = LinearMap (fromList [1, 2, 3, 4] :: M 2 2)

idC2 :: C 2 +> C 2
idC2 = arr (Cat.id :: C 2 -+> C 2)

e0, e1 :: C 2
e0 = fromList [1, 0]
e1 = fromList [0, 1]

showT t = show (HM.flatten (extract (getTensorProduct t)))

main :: IO ()
main = do
  putStrLn $ "f e0 = " ++ show (extract (f $ e0)) ++ "   (expect [1,3])"
  putStrLn $ "f e1 = " ++ show (extract (f $ e1)) ++ "   (expect [2,4])"
  putStrLn ""
  putStrLn "-- (f ⊗^ id) on basis tensors; expect (f eᵢ) ⊗ eⱼ --"
  mapM_
    (\(i, ei) -> mapM_
      (\(j, ej) -> do
        let lhs = (f ⊗^ idC2) $ (ei ⊗ ej)
            rhs = (f $ ei) ⊗ ej
        putStrLn $ "(f⊗id)(e" ++ show i ++ "⊗e" ++ show j ++ ") = " ++ showT lhs
                 ++ "   expect " ++ showT rhs)
      [(0 :: Int, e0), (1, e1)])
    [(0 :: Int, e0), (1, e1)]
  putStrLn ""
  putStrLn "-- (id ⊗^ f) on basis tensors; expect eᵢ ⊗ (f eⱼ) --"
  mapM_
    (\(i, ei) -> mapM_
      (\(j, ej) -> do
        let lhs = (idC2 ⊗^ f) $ (ei ⊗ ej)
            rhs = ei ⊗ (f $ ej)
        putStrLn $ "(id⊗f)(e" ++ show i ++ "⊗e" ++ show j ++ ") = " ++ showT lhs
                 ++ "   expect " ++ showT rhs)
      [(0 :: Int, e0), (1, e1)])
    [(0 :: Int, e0), (1, e1)]
  putStrLn ""
  putStrLn "-- composition g . h pointwise --"
  let g = LinearMap (fromList [0, 1 :+ 1, 1, 0] :: M 2 2) :: C 2 +> C 2
      x = fromList [1, 2 :+ 1] :: C 2
  putStrLn $ "(g.f) x   = " ++ show (extract ((g . f) $ x))
  putStrLn $ "g (f x)   = " ++ show (extract (g $ (f $ x)))
  putStrLn ""
  putStrLn "-- composition with a tensor-domain map: k : (C2⊗C2) +> C2 --"
  -- k built via raw LinearMap over konst-like storage is what productMPS does;
  -- here use explicit columns through linMapFromColumnImages-like route:
  let k = LinearMap (fromList [1, 2, 3, 4, 5, 6, 7, 8]) :: (C 2 ⊗ C 2) +> C 2
      v2 = fromList [1, 2] :: C 2
      w2 = fromList [10, 30] :: C 2
      vw = v2 ⊗ w2
  putStrLn $ "storage(v⊗w)     = " ++ showT vw
  mapM_
    (\(i, ei) -> mapM_
      (\(j, ej) ->
        putStrLn $ "k(e" ++ show i ++ "⊗e" ++ show j ++ ") = " ++ show (extract (k $ (ei ⊗ ej))))
      [(0 :: Int, e0), (1, e1)])
    [(0 :: Int, e0), (1, e1)]
  putStrLn $ "k (v⊗w)          = " ++ show (extract (k $ vw))
  putStrLn $ "(g.k) (v⊗w)      = " ++ show (extract ((g . k) $ vw))
  putStrLn $ "g (k (v⊗w))      = " ++ show (extract (g $ (k $ vw)))
  putStrLn $ "(k.(f⊗^id))(v⊗w) = " ++ show (extract ((k . (f ⊗^ idC2)) $ vw))
  putStrLn $ "k ((f⊗^id)(v⊗w)) = " ++ show (extract (k $ ((f ⊗^ idC2) $ vw)))
