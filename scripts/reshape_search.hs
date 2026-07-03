{-# LANGUAGE DataKinds, TypeOperators, TypeApplications #-}
import Prelude hiding (id, ($))
import Control.Arrow.Constrained (($), arr)
import Math.LinearMap.Category (type (⊗), type (+>), (⊗), transposeTensor, getLinearFunction, getTensorProduct, Tensor (..), LinearMap (..))
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.Orphans ()
import Numeric.LinearAlgebra.Static (R, Sized (fromList), extract)
import qualified Numeric.LinearAlgebra as HM

f :: Bool -> Int -> HM.Vector Double -> HM.Matrix Double
f trS c v = (if trS then HM.tr else id) (HM.reshape c v)

main :: IO ()
main = do
  let n = 2 :: Int
      du = 3
      dw = 6
      xy = fromList [1, 2] ⊗ fromList [3, 4, 5] :: R 2 ⊗ R 3
      ref = getLinearFunction transposeTensor xy
      refVec = HM.toList $ HM.flatten (extract (getTensorProduct ref))
      tvec = HM.flatten (extract xy)
      lm = extract (getLinearMap (arr transposeTensor :: (R 2 ⊗ R 3) +> (R 3 ⊗ R 2))) :: HM.Matrix Double
      (nr, nc) = HM.size lm
  putStrLn $ "lm size: " ++ show (nr, nc)
  putStrLn $ "tvec: " ++ show (HM.toList tvec)
  putStrLn $ "ref: " ++ show refVec
  let cols = HM.toColumns lm
      rows = HM.toRows lm
      hcatTry c trS =
        HM.toList $ (foldl1 HM.||| (map (f trS c) cols)) HM.#> tvec
      vcatTry c trS =
        HM.toList $ (foldl1 HM.=== (map (f trS c) cols)) HM.#> tvec
      rowTry c trS =
        HM.toList $ (foldl1 HM.||| (map (f trS c) rows)) HM.#> tvec
      flatTries =
        [ ("direct", HM.toList $ lm HM.#> tvec)
        , ("tr lm", HM.toList $ HM.tr lm HM.#> tvec)
        , ("reshape (du*n) flat", HM.toList $ HM.reshape (du * n) (HM.flatten lm) HM.#> tvec)
        , ("reshape dw flat", HM.toList $ HM.reshape dw (HM.flatten lm) HM.#> tvec)
        ]
      hcatTries =
        [ ( "hcat reshape " ++ show c ++ " col tr=" ++ show trS, hcatTry c trS)
        | c <- [du, dw, n, du * n, dw * n]
        , trS <- [False, True]
        ]
      vcatTries =
        [ ( "vcat reshape " ++ show c ++ " col tr=" ++ show trS, vcatTry c trS)
        | c <- [du, dw, n, du * n, dw * n]
        , trS <- [False, True]
        ]
      rowTries =
        [ ( "hcat reshape " ++ show c ++ " row tr=" ++ show trS, rowTry c trS)
        | c <- [du, dw, n, du * n, dw * n]
        , trS <- [False, True]
        ]
      tries = flatTries ++ hcatTries ++ vcatTries ++ rowTries
      matches = filter (\(_, rv) -> rv == refVec) tries
  mapM_ (\(name, rv) -> putStrLn $ "MATCH: " ++ name ++ " -> " ++ show rv) matches
  putStrLn $ "found " ++ show (length matches) ++ " matches"
