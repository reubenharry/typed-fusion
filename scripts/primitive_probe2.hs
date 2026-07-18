{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Narrow down which C-backend primitive breaks tensor-shaped maps:
--   (a) arr of a tensor-valued LinearFunction ('sampleLinearFunction')
--   (b) composeLinear with a tensor domain
--   (c) composeLinear with a tensor codomain
import Prelude hiding (($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($), arr)
import Data.Complex (Complex ((:+)))
import Numeric.LinearAlgebra.Static (C, M, extract, Sized (fromList))
import Math.LinearMap.Category
  ( type (+>), type (-+>), type (⊗), (⊗), Tensor (getTensorProduct)
  , LinearMap (LinearMap), TensorSpace (transposeTensor, fmapTensor)
  , LinearSpace (applyLinear), (-+$>) )
import qualified Numeric.LinearAlgebra as HM
import TensorNetwork.MPS.General ()

showT :: (C 2 ⊗ C 2) -> String
showT t = show (HM.toList (HM.flatten (extract (getTensorProduct t))))

e0, e1, v, w :: C 2
e0 = fromList [1, 0]
e1 = fromList [0, 1]
v = fromList [1, 2]
w = fromList [10, 30]

f :: C 2 +> C 2
f = LinearMap (fromList [1, 2, 3, 4] :: M 2 2)

basisT :: [(String, C 2 ⊗ C 2)]
basisT =
  [ ("e0⊗e0", e0 ⊗ e0), ("e0⊗e1", e0 ⊗ e1)
  , ("e1⊗e0", e1 ⊗ e0), ("e1⊗e1", e1 ⊗ e1) ]

main :: IO ()
main = do
  putStrLn "== (a) arr transposeTensor as a LinearMap =="
  let mT = arr (transposeTensor :: (C 2 ⊗ C 2) -+> (C 2 ⊗ C 2)) :: (C 2 ⊗ C 2) +> (C 2 ⊗ C 2)
  mapM_ (\(nm, t) -> putStrLn $ "  arrT " ++ nm ++ " = " ++ showT (mT $ t)
                     ++ "   direct = " ++ showT (transposeTensor -+$> t)) basisT
  putStrLn ""
  putStrLn "== (a') arr (fmapTensor f) as a LinearMap =="
  let fLin = applyLinear -+$> f :: C 2 -+> C 2
      mF = arr ((fmapTensor -+$> fLin) :: (C 2 ⊗ C 2) -+> (C 2 ⊗ C 2)) :: (C 2 ⊗ C 2) +> (C 2 ⊗ C 2)
  mapM_ (\(nm, t) -> putStrLn $ "  arrF " ++ nm ++ " = " ++ showT (mF $ t)
                     ++ "   direct = " ++ showT ((fmapTensor -+$> fLin) -+$> t)) basisT
  putStrLn ""
  putStrLn "== (b) tensor-endo composition: (mT . mT) should be identity =="
  mapM_ (\(nm, t) -> putStrLn $ "  (mT.mT) " ++ nm ++ " = " ++ showT ((mT . mT) $ t)) basisT
  putStrLn ""
  putStrLn "== (b') (mF . mT) pointwise vs stepwise =="
  mapM_ (\(nm, t) -> putStrLn $ "  (mF.mT) " ++ nm ++ " = " ++ showT ((mF . mT) $ t)
                     ++ "   stepwise = " ++ showT (mF $ (mT $ t))) basisT
  putStrLn ""
  putStrLn "== (c) tensor-domain composition: (g . k) basis images =="
  let k = LinearMap (fromList [1, 2, 3, 4, 5, 6, 7, 8]) :: (C 2 ⊗ C 2) +> C 2
      g = LinearMap (fromList [0, 1 :+ 1, 1, 0] :: M 2 2) :: C 2 +> C 2
  mapM_ (\(nm, t) -> putStrLn $ "  (g.k) " ++ nm ++ " = " ++ show (extract ((g . k) $ t))
                     ++ "   g(k " ++ nm ++ ") = " ++ show (extract (g $ (k $ t)))) basisT
