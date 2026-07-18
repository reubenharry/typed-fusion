{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

import Prelude hiding (($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($), arr)
import Data.Complex (realPart)
import Data.VectorSpace (InnerSpace ((<.>)), (^-^))
import Numeric.LinearAlgebra.Static (C, Sized (fromList))
import Math.LinearMap.Category
  ( type (+>), type (-+>), type (⊗), (⊗)
  , TensorSpace (transposeTensor), (-+$>)
  )
import Numeric.LinearAlgebra.Static.COrphans ()
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()

e0, e1 :: C 2
e0 = fromList [1, 0]
e1 = fromList [0, 1]

nrm :: (C 2 ⊗ C 2) -> Double
nrm t = sqrt (realPart (t <.> t))

main :: IO ()
main = do
  let idT = arr (Cat.id :: (C 2 ⊗ C 2) -+> (C 2 ⊗ C 2)) :: (C 2 ⊗ C 2) +> (C 2 ⊗ C 2)
      mT = arr (transposeTensor :: (C 2 ⊗ C 2) -+> (C 2 ⊗ C 2)) :: (C 2 ⊗ C 2) +> (C 2 ⊗ C 2)
  mapM_
    (\(nm, t) ->
       putStrLn $
         nm
           ++ "  ||idT t - t||="
           ++ show (nrm ((idT $ t) ^-^ t))
           ++ "  ||arr tr t - tr t||="
           ++ show (nrm ((mT $ t) ^-^ (transposeTensor -+$> t))))
    [("e0⊗e0", e0 ⊗ e0), ("e0⊗e1", e0 ⊗ e1), ("e1⊗e0", e1 ⊗ e0), ("e1⊗e1", e1 ⊗ e1)]
