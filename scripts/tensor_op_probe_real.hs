{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}

-- | Same probe as tensor_op_probe.hs but on the real (R n) backend.
import Prelude hiding (($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($), arr)
import Numeric.LinearAlgebra.Static (R, L, extract, Sized (fromList))
import Math.LinearMap.Category
  (type (+>), type (-+>), type (⊗), (⊗), Tensor (getTensorProduct), LinearMap (LinearMap))
import qualified Numeric.LinearAlgebra as HM
import Numeric.LinearAlgebra.Static.Orphans ()
import Math.LinearMap.Category.Instances ()
import TensorNetwork.Categorical ((⊗^))

f :: R 2 +> R 2
f = LinearMap (fromList [1, 2, 3, 4] :: L 2 2)

idR2 :: R 2 +> R 2
idR2 = arr (Cat.id :: R 2 -+> R 2)

e0, e1 :: R 2
e0 = fromList [1, 0]
e1 = fromList [0, 1]

showT t = show (HM.flatten (extract (getTensorProduct t)))

main :: IO ()
main = do
  putStrLn $ "f e0 = " ++ show (extract (f $ e0)) ++ "   (expect [1,3])"
  putStrLn "-- (f ⊗^ id) on basis tensors; expect (f eᵢ) ⊗ eⱼ --"
  mapM_
    (\(i, ei) -> mapM_
      (\(j, ej) -> do
        let lhs = (f ⊗^ idR2) $ (ei ⊗ ej)
            rhs = (f $ ei) ⊗ ej
        putStrLn $ "(f⊗id)(e" ++ show i ++ "⊗e" ++ show j ++ ") = " ++ showT lhs
                 ++ "   expect " ++ showT rhs)
      [(0 :: Int, e0), (1, e1)])
    [(0 :: Int, e0), (1, e1)]
  putStrLn "-- composition with a tensor-domain map: k : (R2⊗R2) +> R2 --"
  let k = LinearMap (fromList [1, 2, 3, 4, 5, 6, 7, 8]) :: (R 2 ⊗ R 2) +> R 2
      g = LinearMap (fromList [0, 1, 1, 0] :: L 2 2) :: R 2 +> R 2
      vw = (fromList [1, 2] :: R 2) ⊗ (fromList [10, 30] :: R 2)
  putStrLn $ "k (v⊗w)          = " ++ show (extract (k $ vw))
  putStrLn $ "(g.k) (v⊗w)      = " ++ show (extract ((g . k) $ vw))
  putStrLn $ "g (k (v⊗w))      = " ++ show (extract (g $ (k $ vw)))
  putStrLn $ "(k.(f⊗^id))(v⊗w) = " ++ show (extract ((k . (f ⊗^ idR2)) $ vw))
  putStrLn $ "k ((f⊗^id)(v⊗w)) = " ++ show (extract (k $ ((f ⊗^ idR2) $ vw)))
