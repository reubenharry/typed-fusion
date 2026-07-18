{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}

-- | Which layout world does recomposeSB/enumerateSubBasis (the groundState
-- path) live in: the ⊗/apply world or the compose/arr world?
import Prelude hiding (($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($), arr)
import Data.Complex (Complex ((:+)), realPart)
import Data.VectorSpace (InnerSpace ((<.>)))
import Numeric.LinearAlgebra.Static (C, M, extract, Sized (fromList))
import Math.LinearMap.Category
  ( type (+>), type (-+>), type (⊗), (⊗), Tensor (getTensorProduct)
  , LinearMap (LinearMap)
  , FiniteDimensional (entireBasis, enumerateSubBasis, recomposeSB), SubBasis )
import qualified Numeric.LinearAlgebra as HM
import TensorNetwork.MPS.General ()

e0, e1 :: C 2
e0 = fromList [1, 0]
e1 = fromList [0, 1]

basisT :: [(String, C 2 ⊗ C 2)]
basisT =
  [ ("e0⊗e0", e0 ⊗ e0), ("e0⊗e1", e0 ⊗ e1)
  , ("e1⊗e0", e1 ⊗ e0), ("e1⊗e1", e1 ⊗ e1) ]

type Site = (C 2 ⊗ C 2) +> C 2

main :: IO ()
main = do
  putStrLn "== enumerateSubBasis of (C2⊗C2): which ⊗-basis order? =="
  let tb = enumerateSubBasis (entireBasis :: SubBasis (C 2 ⊗ C 2))
  mapM_ (\t -> putStrLn $ "  basis el storage = "
          ++ show (HM.toList (HM.flatten (extract (getTensorProduct t))))) tb
  putStrLn ""
  putStrLn "== inner products of ⊗-built basis under <.> =="
  mapM_ (\(nm, t) ->
      putStrLn $ "  <" ++ nm ++ "|" ++ nm ++ "> = "
        ++ show (t <.> t)) basisT
  putStrLn ""
  putStrLn "== recomposeSB a Site from coordinates 1..8, then apply =="
  let (site, _) = recomposeSB (entireBasis :: SubBasis Site) [1, 2, 3, 4, 5, 6, 7, 8]
        :: (Site, [Complex Double])
  mapM_ (\(nm, t) -> putStrLn $ "  site " ++ nm ++ " = " ++ show (extract (site $ t))) basisT
  putStrLn ""
  putStrLn "== same Site raw: LinearMap (fromList [1..8]) apply =="
  let raw = LinearMap (fromList [1, 2, 3, 4, 5, 6, 7, 8]) :: Site
  mapM_ (\(nm, t) -> putStrLn $ "  raw  " ++ nm ++ " = " ++ show (extract (raw $ t))) basisT
  putStrLn ""
  putStrLn "== <.> between the two: consistent coordinates? =="
  putStrLn $ "  site <.> site = " ++ show (site <.> site)
  putStrLn $ "  raw  <.> raw  = " ++ show (raw <.> raw)
  putStrLn $ "  site <.> raw  = " ++ show (site <.> raw)
