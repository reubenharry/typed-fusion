{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Does arr id act as identity under application? (tensor domain)
import Prelude hiding (($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($), arr)
import Numeric.LinearAlgebra.Static (C, extract, Sized (fromList))
import Math.LinearMap.Category
  ( type (+>), type (-+>), type (⊗), (⊗), Tensor (getTensorProduct) )
import qualified Numeric.LinearAlgebra as HM
import Numeric.LinearAlgebra.Static.COrphans ()
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()

e0, e1 :: C 2
e0 = fromList [1, 0]
e1 = fromList [0, 1]

showT t = show (HM.toList (HM.flatten (extract (getTensorProduct t))))

main :: IO ()
main = do
  let idT = arr (Cat.id :: (C 2 ⊗ C 2) -+> (C 2 ⊗ C 2)) :: (C 2 ⊗ C 2) +> (C 2 ⊗ C 2)
  mapM_ (\(nm,t) -> putStrLn $ nm
          ++ "  idT= " ++ showT (idT $ t)
          ++ "  raw= " ++ showT t
          ++ "  ok? " ++ show (showT (idT $ t) == showT t))
    [("e0⊗e0", e0⊗e0), ("e0⊗e1", e0⊗e1), ("e1⊗e0", e1⊗e0), ("e1⊗e1", e1⊗e1)]
