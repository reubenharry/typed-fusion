{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
-- |
-- Real analogue of 'apply_mre': @R 2 +> (R 3 ⊗ R 2)@ application paths.
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Prelude hiding (($))
import GHC.TypeLits (KnownNat, natVal)
import Data.Proxy (Proxy (..))
import Data.Vector.Storable (Vector)
import qualified Data.Vector.Storable as VS
import Data.VectorSpace ()
import Control.Arrow.Constrained (($))
import Control.Arrow.Constrained (arr)
import Math.LinearMap.Category
  ( type (+>), type (⊗), (⊗), FiniteDimensional (..), SubBasis
  , recomposeLinMap, entireBasis, applyLinear, getLinearFunction, (-+$>)
  , getLinearMap, LinearMap (..) )
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.Orphans ()
import Numeric.LinearAlgebra.Static (R, Sized (fromList, unwrap, extract))
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray, unsafeFromArrayWithOffset)
import qualified Numeric.LinearAlgebra.HMatrix as HM

basisR :: forall n. KnownNat n => Int -> R n
basisR i =
  fromList [ if k == i then 1 else 0 | k <- [0 .. fromIntegral (natVal @n Proxy) - 1] ]

showVec :: Vector Double -> String
showVec = show . VS.toList

(=~=) :: (Eq a) => a -> a -> Bool
a =~= b = a == b

manualRowDecode :: HM.Vector Double -> R 3 ⊗ R 2
manualRowDecode col =
  unsafeFromArray @(R 3 ⊗ R 2) (HM.fromList (HM.toList col))

-- R static linmaps store basis images as /columns/ (see 'recomposeLinMap');
-- 'applyLinear' is @unsafeFromArray . extract $ m#>v@.
manualApply
  :: HM.Matrix Double
  -> R 2
  -> R 3 ⊗ R 2
manualApply mat v =
  unsafeFromArray @(R 3 ⊗ R 2) (HM.fromList (HM.toList (mat HM.#> unwrap v)))

reportPath :: String -> R 3 ⊗ R 2 -> R 3 ⊗ R 2 -> IO ()
reportPath name got expected = do
  let ok = got =~= expected
  putStrLn $ name ++ ": " ++ if ok then "OK" else "MISMATCH"
  unless ok $ do
    putStrLn $ "  expected toArray: " ++ showVec (toArray expected)
    putStrLn $ "  got      toArray: " ++ showVec (toArray got)

unless :: Bool -> IO () -> IO ()
unless b io = if b then pure () else io

main :: IO ()
main = do
  putStrLn "=== applyLinear MRE (ℝ): R 2 +> (R 3 ⊗ R 2) ==="
  putStrLn ""

  let x0, x1 :: R 3
      x0 = fromList [1, 0, 2]
      x1 = fromList [0, 1, -1]
      y0, y1 :: R 2
      y0 = fromList [1, 2]
      y1 = fromList [0, 1]
      imgs :: [R 3 ⊗ R 2]
      imgs = [x0 ⊗ y0, x1 ⊗ y1]

  putStrLn "Ground-truth images:"
  mapM_ (\(j, img) -> putStrLn $ "  img[" ++ show j ++ "] = " ++ showVec (toArray img))
        (zip [0 :: Int ..] imgs)
  putStrLn ""

  let m :: R 2 +> (R 3 ⊗ R 2)
      m = fst (recomposeLinMap (entireBasis :: SubBasis (R 2)) imgs)
      mat = extract (getLinearMap m)

  putStrLn "Storage columns (flat, length 6 each):"
  mapM_ (\j -> putStrLn $ "  col " ++ show j ++ " = " ++ show (HM.toList (HM.toColumns mat !! j)))
        [0, 1]
  putStrLn ""

  putStrLn "=== decode-only ==="
  mapM_ (\j -> do
    let col = HM.toColumns mat !! j
        viaExplicit = manualRowDecode col
        viaMono = unsafeFromArrayWithOffset 0 (HM.fromList (HM.toList col))
    putStrLn $ "col " ++ show j ++ ": explicit unsafeFromArray == img: "
      ++ (if viaExplicit =~= (imgs !! j) then "OK" else "FAIL")
    putStrLn $ "col " ++ show j ++ ": monomorphic WithOffset  == img: "
      ++ (if viaMono =~= (imgs !! j) then "OK" else "FAIL")
    ) [0, 1]
  putStrLn ""

  mapM_ (\j -> do
    let v = basisR @2 j
        expected = imgs !! j
        viaManual = manualApply mat v
        viaApplyLinear = getLinearFunction (applyLinear -+$> m) v
        viaDollar = m $ v
        viaArr = arr m v
    putStrLn $ "--- basis index j = " ++ show j ++ " ---"
    reportPath "manual row-sum" viaManual expected
    reportPath "getLinearFunction (applyLinear m)" viaApplyLinear expected
    reportPath "m $ v" viaDollar expected
    reportPath "arr m v" viaArr expected
    putStrLn ""
    ) [0, 1]

  putStrLn "=== control: R 2 +> R 3 (vector codomain) ==="
  let imgs3 = [x0, x1] :: [R 3]
      m3 :: R 2 +> R 3
      m3 = fst (recomposeLinMap (entireBasis :: SubBasis (R 2)) imgs3)
  mapM_ (\j -> do
    let v = basisR @2 j
        expected = imgs3 !! j
        got = m3 $ v
        gotAL = getLinearFunction (applyLinear -+$> m3) v
    putStrLn $ "j=" ++ show j
      ++ "  m$=" ++ (if got =~= expected then "OK" else "FAIL")
      ++ "  applyLinear=" ++ (if gotAL =~= expected then "OK" else "FAIL")
    ) [0, 1]
