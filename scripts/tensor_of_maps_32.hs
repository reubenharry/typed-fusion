{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}

-- | tensorOfMaps on unequal factors C3 ⊗ C2
import Prelude hiding (($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($), arr)
import Data.Complex (realPart)
import Data.VectorSpace (InnerSpace ((<.>)), (^-^))
import Numeric.LinearAlgebra.Static (C, M, extract, Sized (fromList))
import Math.LinearMap.Category
  ( type (+>), type (-+>), type (⊗), (⊗), Tensor (getTensorProduct)
  , LinearMap (LinearMap), tensorOfMaps, (-+$>)
  )
import qualified Numeric.LinearAlgebra as HM
import Numeric.LinearAlgebra.Static.COrphans ()
import Math.LinearMap.Category.Backend.HMatrix ()
import TensorNetwork.Categorical ((⊗^))

e0_3, e1_3 :: C 3
e0_3 = fromList [1, 0, 0]
e1_3 = fromList [0, 1, 0]

e0_2, e1_2 :: C 2
e0_2 = fromList [1, 0]
e1_2 = fromList [0, 1]

f :: C 3 +> C 3
f = LinearMap (fromList [1, 0, 0, 0, 2, 0, 0, 0, 3] :: M 3 3)  -- diag(1,2,3)

id2 :: C 2 +> C 2
id2 = arr (Cat.id :: C 2 -+> C 2)

diff t1 t2 =
  let d = t1 ^-^ t2
  in sqrt (realPart (d <.> d))

main :: IO ()
main = do
  let lhs = (f ⊗^ id2) $ (e0_3 ⊗ e1_2)
      rhs = (f $ e0_3) ⊗ e1_2
  putStrLn $ "err (f⊗id)(e0⊗e1) = " ++ show (diff lhs rhs)
  let lhs2 = ((tensorOfMaps -+$> f) -+$> id2) $ (e1_3 ⊗ e0_2)
      rhs2 = (f $ e1_3) ⊗ e0_2
  putStrLn $ "err (f⊗id)(e1⊗e0) = " ++ show (diff lhs2 rhs2)
  putStrLn $ "lhs storage = " ++ show (HM.toList (HM.flatten (extract (getTensorProduct lhs))))
  putStrLn $ "rhs storage = " ++ show (HM.toList (HM.flatten (extract (getTensorProduct rhs))))
