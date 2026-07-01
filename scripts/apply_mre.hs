{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
-- |
-- Minimal repro: @C 2 +> (C 3 ⊗ C 2)@ application paths on a map with known images.
--
-- Map construction uses 'recomposeLinMap' only to assemble storage from two
-- explicit images (test setup). What we compare is /application/:
--   manual row-sum  vs  'applyLinear'  vs  morphism @($)@.
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Prelude hiding (($))
import GHC.TypeLits (KnownNat, natVal)
import Data.Proxy (Proxy (..))
import Data.Complex (Complex ((:+)))
import Data.Vector.Storable (Vector)
import qualified Data.Vector.Storable as VS
import Data.VectorSpace ()
import Control.Arrow.Constrained (($))
import Control.Arrow.Constrained (arr)
import Math.LinearMap.Category
  ( type (+>), type (⊗), (⊗), FiniteDimensional (..), SubBasis
  , recomposeLinMap, entireBasis, applyLinear, getLinearFunction, (-+$>)
  , getLinearMap, LinearMap (..), TensorSpace, Scalar )
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, Sized (fromList, unwrap, extract))
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray, unsafeFromArrayWithOffset)
import qualified Numeric.LinearAlgebra.HMatrix as HM

--------------------------------------------------------------------------------
-- Tiny helpers (no quantum package)
--------------------------------------------------------------------------------

basisC :: forall n. KnownNat n => Int -> C n
basisC i =
  fromList [ if k == i then 1 else 0 | k <- [0 .. fromIntegral (natVal @n Proxy) - 1] ]

showVec :: VS.Vector (Complex Double) -> String
showVec = show . VS.toList

(=~=) :: (Eq a) => a -> a -> Bool
a =~= b = a == b

--------------------------------------------------------------------------------
-- Application paths under test
--------------------------------------------------------------------------------

manualRowDecode :: HM.Vector (Complex Double) -> C 3 ⊗ C 2
manualRowDecode row =
  unsafeFromArray @(C 3 ⊗ C 2) (HM.fromList (HM.toList row))

manualApply
  :: HM.Matrix (Complex Double)
  -> C 2
  -> C 3 ⊗ C 2
manualApply mat v =
  unsafeFromArray @(C 3 ⊗ C 2) (HM.fromList (HM.toList (mat HM.#> unwrap v)))

reportPath :: String -> C 3 ⊗ C 2 -> C 3 ⊗ C 2 -> IO ()
reportPath name got expected = do
  let ok = got =~= expected
  putStrLn $ name ++ ": " ++ if ok then "OK" else "MISMATCH"
  unless ok $ do
    putStrLn $ "  expected toArray: " ++ showVec (toArray expected)
    putStrLn $ "  got      toArray: " ++ showVec (toArray got)

unless :: Bool -> IO () -> IO ()
unless b io = if b then pure () else io

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== applyLinear MRE: C 2 +> (C 3 ⊗ C 2) ==="
  putStrLn ""

  -- Two explicit codomain images (known ground truth).
  let x0, x1 :: C 3
      x0 = fromList [1 :+ 0, 0 :+ 1, 2 :+ 0]
      x1 = fromList [0 :+ 1, 1 :+ 0, (-1) :+ 1]
      y0, y1 :: C 2
      y0 = fromList [1 :+ 0, 2 :+ (-1)]
      y1 = fromList [0 :+ 1, 1 :+ 1]
      imgs :: [C 3 ⊗ C 2]
      imgs = [x0 ⊗ y0, x1 ⊗ y1]

  putStrLn "Ground-truth images (recomposed map should apply to these):"
  mapM_ (\(j, img) -> putStrLn $ "  img[" ++ show j ++ "] = " ++ showVec (toArray img))
        (zip [0 :: Int ..] imgs)
  putStrLn ""

  -- Assemble LinearMap from images (setup only).
  let m :: C 2 +> (C 3 ⊗ C 2)
      m = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs)
      storage = getLinearMap m
      mat = extract storage

  putStrLn "Storage columns (flat, length 6 each):"
  mapM_ (\i -> putStrLn $ "  col " ++ show i ++ " = " ++ show (HM.toList (HM.toColumns mat !! i)))
        [0, 1]
  putStrLn ""

  putStrLn "=== decode-only ==="
  mapM_ (\i -> do
    let col = HM.toColumns mat !! i
        flatFromCol = HM.toList col
        flatFromApply = HM.toList (mat HM.#> unwrap (basisC @2 i))
        viaExplicit = manualRowDecode col
        viaMono = unsafeFromArrayWithOffset 0 (HM.fromList flatFromCol)
        viaClass = manualApply mat (basisC @2 i)
    putStrLn $ "col " ++ show i ++ ": explicit unsafeFromArray == img: "
      ++ (if viaExplicit =~= (imgs !! i) then "OK" else "FAIL")
    putStrLn $ "col " ++ show i ++ ": monomorphic WithOffset  == img: "
      ++ (if viaMono =~= (imgs !! i) then "OK" else "FAIL")
    putStrLn $ "col " ++ show i ++ ": manualApply(#>v) == img: "
      ++ (if viaClass =~= (imgs !! i) then "OK" else "FAIL")
    ) [0, 1]
  putStrLn ""

  mapM_ (\j -> do
    let v = basisC @2 j
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

  putStrLn "=== control: C 2 +> C 3 (vector codomain, same domain) ==="
  let imgs3 = [x0, x1] :: [C 3]
      m3 :: C 2 +> C 3
      m3 = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) imgs3)
  mapM_ (\j -> do
    let v = basisC @2 j
        expected = imgs3 !! j
        got = m3 $ v
        gotAL = getLinearFunction (applyLinear -+$> m3) v
    putStrLn $ "j=" ++ show j
      ++ "  m$=" ++ (if got =~= expected then "OK" else "FAIL")
      ++ "  applyLinear=" ++ (if gotAL =~= expected then "OK" else "FAIL")
    ) [0, 1]
