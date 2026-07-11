{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{- HLINT ignore "Redundant $" -}
import Prelude hiding (id, ($))
import Control.Category.Constrained (id)
import Control.Arrow.Constrained (($), arr)
import TensorNetwork.Categorical ((⊗^), swapMap)
import Math.LinearMap.Category
  ( type (+>), type (⊗), (⊗), FiniteDimensional (..), SubBasis
  , LinearMap (..), decomposeLinMap, recomposeLinMap, Tensor (..)
  , transposeTensor, fmapTensor, applyLinear, tensorOfMaps, tensorDomainSample
  , getLinearFunction, (-+$>), type (-+>), LinearFunction, lfun )
import Control.Exception (try, SomeException, evaluate)
import Control.Monad (when)
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static.Orphans ()
import Numeric.LinearAlgebra.Static (C, R, M, Sized (..), extract, L)
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray, Dimension)
import qualified Numeric.LinearAlgebra.HMatrix as HM
import GHC.TypeLits (KnownNat, natVal)
import Data.Proxy (Proxy (..))
import Data.Complex (Complex ((:+)))
import Unsafe.Coerce (unsafeCoerce)
import qualified Data.Vector.Storable as VS
import Linear.V2 (V2 (..))
import Linear.V3 (V3 (..))
import Math.LinearMap.Category.Class (LinearSpace(..))
import Data.AdditiveGroup (AdditiveGroup(..))
import Linear (V4)
import Numeric.LinearAlgebra (tr)

type ℂ = Complex Double

one1 :: C 1
one1 = fromList [1]

basisAt :: forall n. KnownNat n => Int -> C n
basisAt i =
  fromList [ if j == i then 1 else 0 | j <- [0 .. fromIntegral (natVal (Proxy @n)) - 1] ]

basisAtR :: forall n. KnownNat n => Int -> R n
basisAtR i =
  fromList [ if j == i then 1 else 0 | j <- [0 .. fromIntegral (natVal (Proxy @n)) - 1] ]

-- | Minimal repro: @applyLinear (arr transposeTensor)@ should match @getLinearFunction transposeTensor@.
-- Uses default @sampleLinearFunction@ via @arr@ (not @tensorDomainSample@).
-- import qualified Numeric.LinearAlgebra as LA

-- reshapeSearch :: IO ()
-- reshapeSearch = do
--   let n = 2 :: Int
--       du = 3
--       xy = fromList [1, 2] ⊗ fromList [3, 4, 5] :: R 2 ⊗ R 3
--       ref = getLinearFunction transposeTensor xy
--       refVec = LA.toList $ LA.flatten (extract (getTensorProduct ref))
--       tvec = LA.flatten (extract xy)
--       lm = extract (getLinearMap (arr transposeTensor :: (R 2 ⊗ R 3) +> (R 3 ⊗ R 2)))
--   putStrLn $ "lm size: " ++ show (LA.size lm)
--   putStrLn $ "tvec: " ++ show (LA.toList tvec)
--   putStrLn $ "ref: " ++ show refVec
--   let cols = LA.toColumns lm
--       rows = LA.toRows lm
--       blk' trS c v = (if trS then LA.tr else (\m -> m)) (LA.reshape c v)
--       hcat c trS = LA.toList $ (foldl1 (LA.|||) (map (blk' trS c) cols)) LA.#> tvec
--       tries =
--         [ ("direct", LA.toList $ lm LA.#> tvec)
--         , ("tr lm", LA.toList $ LA.tr lm LA.#> tvec)
--         , ("flat du*n", LA.toList $ LA.reshape (du * n) (LA.flatten lm) LA.#> tvec)
--         ] ++ [ ("hcat c=" ++ show c ++ " tr=" ++ show trS, hcat c trS)
--              | c <- [du, 6, n, du*n, 3*n]
--              , trS <- [False, True] ]
--           ++ [ ("hcat-row c=" ++ show c ++ " tr=" ++ show trS
--                , LA.toList $ (foldl1 (LA.|||) (map (blk' trS c) rows)) LA.#> tvec)
--              | c <- [du, 6, n, du*n, 3*n]
--              , trS <- [False, True] ]
--   mapM_ (\(nm, rv) -> when (rv == refVec) $ putStrLn $ "MATCH " ++ nm) tries
--   putStrLn "reshape search done"


minimalTest :: IO ()
minimalTest = do
  putStrLn "\n=== minimal transposeTensor (R) ==="
  let xy = fromList [1, 2] ⊗ fromList [3, 4, 5, 6] :: R 2 ⊗ R 3
      badMap = LinearMap (konst 1 :: L 12 2) :: (R 2 ⊗ R 3) +> R 4
      -- application = badMap $ xy
      rawMat = (extract (getLinearMap badMap))
      reshapedMat = HM.reshape 6 (HM.flatten rawMat)
      -- application =  (extract (getLinearMap badMap)) HM.#> (HM.flatten (extract (getTensorProduct xy)))
      -- application =  (reshapedMat) HM.#> (HM.flatten (extract (getTensorProduct xy)))
      -- application = getLinearFunction (applyTensorLinMap -+$> badMap) xy
      application = badMap $ xy
  print (show $ application)

minimalTestV :: IO ()
minimalTestV = do
  putStrLn "\n=== minimal transposeTensor (V) ==="
  let xy = (V2 1 2) ⊗ (V3 3 4 5) :: V2 Double ⊗ V3 Double
      badMap = LinearMap (V2 (Tensor (V3 1 1 1)) (Tensor (V3 1 1 1))) :: (V2 Double ⊗ V3 Double) +> V4 Double
      application = badMap $ xy
      -- application = getLinearFunction (applyTensorLinMap -+$> badMap) xy
  print (show $  application)

testTransposeMinimalR :: IO ()
testTransposeMinimalR = do
  putStrLn "\n=== minimal transposeTensor (R) ==="
  let xy = fromList [1, 2] ⊗ fromList [3, 4, 5] :: R 2 ⊗ R 3
      transposeTensorMap = arr transposeTensor :: (R 2 ⊗ R 3) +> (R 3 ⊗ R 2)
      rawMat = getLinearMap transposeTensorMap :: L 18 2
      reshapedMat = HM.reshape 6 (HM.flatten $ tr $ extract rawMat)
      mult = reshapedMat HM.#> (HM.flatten $ extract (getTensorProduct xy))
      bang = transposeTensorMap $ xy
      ref = getLinearFunction transposeTensor xy
  print mult
  print (show $ getTensorProduct bang)
  print (show $ getTensorProduct ref)
  putStrLn $ "arr == getLF (show): " ++ show (show (getTensorProduct bang) == show (getTensorProduct ref))

testTransposeMinimalV :: IO ()
testTransposeMinimalV = do
  putStrLn "\n=== minimal transposeTensor (V) ==="
  let xy = (V2 1 2) ⊗ (V3 3 4 5) :: V2 Double ⊗ V3 Double
      transposeTensorMap = arr transposeTensor :: (V2 Double ⊗ V3 Double) +> (V3 Double ⊗ V2 Double)
      bang = transposeTensorMap $ xy
      ref = getLinearFunction transposeTensor xy
  print (show $ getTensorProduct bang)
  putStrLn $ "arr == getLF (show): " ++ show (show (getTensorProduct bang) == show (getTensorProduct ref))


  -- stepIO "getLinearFunction transposeTensor" $
  --   evaluate (getLinearFunction transposeTensor xy) >> pure ()
  -- stepIO "applyLinear (arr transposeTensor)" $
  --   evaluate ((applyLinear -+$> arr transposeTensor) -+$> xy) >> pure ()
  -- rViaGet <- try @SomeException $ evaluate (getLinearFunction transposeTensor xy :: R 3 ⊗ R 2)
  -- rViaArr <- try @SomeException $ evaluate ((applyLinear -+$> arr transposeTensor) -+$> xy :: R 3 ⊗ R 2)
  -- case (rViaGet, rViaArr) of
  --   (Right viaGet, Right viaArr) ->
  --     putStrLn $ "getLinearFunction == arr: " ++ show (viaGet == viaArr)
  --   (Right viaGet, Left _) -> do
  --     viaGet `seq` putStrLn "getLinearFunction ok; arr path failed (see above)"
  --   _ -> pure ()

testTransposeMinimalC :: IO ()
testTransposeMinimalC = do
  putStrLn "\n=== minimal transposeTensor (C) ==="
  let xy = (basisAt @2 0) ⊗ (basisAt @3 0) :: C 2 ⊗ C 3
  stepIO "getLinearFunction transposeTensor" $
    evaluate (getLinearFunction transposeTensor xy) >> pure ()
  stepIO "applyLinear (arr transposeTensor)" $
    evaluate ((applyLinear -+$> arr transposeTensor) -+$> xy) >> pure ()
  rViaGet <- try @SomeException $ evaluate (getLinearFunction transposeTensor xy :: C 3 ⊗ C 2)
  rViaArr <- try @SomeException $ evaluate ((applyLinear -+$> arr transposeTensor) -+$> xy :: C 3 ⊗ C 2)
  case (rViaGet, rViaArr) of
    (Right viaGet, Right viaArr) ->
      putStrLn $ "getLinearFunction == arr: " ++ show (viaGet == viaArr)
    (Right viaGet, Left _) -> do
      viaGet `seq` putStrLn "getLinearFunction ok; arr path failed (see above)"
    _ -> pure ()

-- main :: IO ()
-- main = do
--   reshapeSearch
--   testTransposeMinimalR
--   testTransposeMinimalV

{-# NOINLINE restOfTensorDebug #-}
restOfTensorDebug :: IO ()
restOfTensorDebug = do
  putStrLn "\n=== atomic C2,C3 step-through ==="
  let f = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) [basisAt @3 0, basisAt @3 1])
        :: C 2 +> C 3
      g = id :: C 3 +> C 3
      x = basisAt @2 0
      y = basisAt @3 0
      xy = x ⊗ y :: C 2 ⊗ C 3
  putStrLn $ "xy tensor matrix: " ++ show (extract (tensorMat xy))
  step "transposeTensor xy" $ extract (tensorMat (getLinearFunction transposeTensor xy)) `seq` ()
  let t1 = getLinearFunction transposeTensor xy :: C 3 ⊗ C 2
  putStrLn $ "t1 matrix: " ++ show (extract (tensorMat t1))
  step "fmapTensor (applyLinear f) t1" $
    extract (tensorMat (getLinearFunction (fmapTensor -+$> (applyLinear -+$> f)) t1)) `seq` ()
  let t2 = getLinearFunction (fmapTensor -+$> (applyLinear -+$> f)) t1 :: C 3 ⊗ C 3
  putStrLn $ "t2 matrix: " ++ show (extract (tensorMat t2))
  step "transposeTensor t2" $ extract (tensorMat (getLinearFunction transposeTensor t2)) `seq` ()
  let t3 = getLinearFunction transposeTensor t2 :: C 3 ⊗ C 3
  step "fmapTensor (applyLinear g) t3" $
    extract (tensorMat (getLinearFunction (fmapTensor -+$> (applyLinear -+$> g)) t3)) `seq` ()
  let tom =
        getLinearFunction (fmapTensor -+$> (applyLinear -+$> g))
          . getLinearFunction transposeTensor
          . getLinearFunction (fmapTensor -+$> (applyLinear -+$> f))
          . getLinearFunction transposeTensor
  stepIO "composed getLinearFunction pipeline" $ evaluate (tom xy) >> pure ()
  stepIO "full (f ⊗^ g) $ xy" $ evaluate ((f ⊗^ g) $ xy) >> pure ()
  putStrLn "\n=== sampleLinearFunction on tensor domain (C, redundant with minimal) ==="
  stepIO "transpose C getLF vs arr" $
    let xy' = xy
        _ = (getLinearFunction transposeTensor xy', (applyLinear -+$> arr transposeTensor) -+$> xy')
    in pure ()
  putStrLn $ "expected matrix: " ++ show (extract (tensorMat ((f $ x) ⊗ (g $ y))))
  putStrLn "\n=== atomic C2,C3 ==="
  let f = fst (recomposeLinMap (entireBasis :: SubBasis (C 2)) [basisAt @3 0, basisAt @3 1])
        :: C 2 +> C 3
      g = id :: C 3 +> C 3
      x = basisAt @2 0
      y = basisAt @3 0
      lhs = (f ⊗^ g) $ (x ⊗ y) :: C 3 ⊗ C 3
      rhs = (f $ x) ⊗ (g $ y) :: C 3 ⊗ C 3
  putStrLn $ "tensorOfMaps lhs == rhs: " ++ show (lhs == rhs)

  let x2 = fromList [2 :+ (-1), 1 :+ 1] :: C 2
      y2 = fromList [0 :+ (-1), 0 :+ 2, (-1) :+ (-2)] :: C 3
      lhsR = (f ⊗^ g) $ (x2 ⊗ y2) :: C 3 ⊗ C 3
      rhsR = (f $ x2) ⊗ (g $ y2) :: C 3 ⊗ C 3
  putStrLn $ "random vec lhs == rhs: " ++ show (lhsR == rhsR)
  putStrLn $ "swap lhs == rhs: " ++ show ((swapMap $ lhsR) == rhsR)
  putStrLn $ "random lhs arr: " ++ show (VS.toList (toArray lhsR :: VS.Vector ℂ))
  putStrLn $ "random rhs arr: " ++ show (VS.toList (toArray rhsR :: VS.Vector ℂ))

  let mf = extract (getLM f)
      mg = extract (getLM g)
      inp = HM.fromList $ VS.toList (toArray (x2 ⊗ y2) :: VS.Vector ℂ)
      out = HM.fromList $ VS.toList (toArray rhsR :: VS.Vector ℂ)
      af = HM.tr' mf
      ag = HM.tr' mg
  putStrLn $ "kron arr random: skipped"
  putStrLn $ "kron arr basis: skipped"

  putStrLn "\n=== site C1⊗C2 ==="
  let sf = fst (recomposeLinMap (entireBasis :: SubBasis (C 1 ⊗ C 2))
        [ basisAt @2 0, basisAt @2 1, basisAt @2 0, basisAt @2 1 ])
        :: (C 1 ⊗ C 2) +> C 2
      sid = id :: C 2 +> C 2
      sx = one1 ⊗ basisAt @2 0
      sy = basisAt @2 0
      lhs2 = (sf ⊗^ sid) $ (sx ⊗ sy)
      rhs2 = (sf $ sx) ⊗ sy
  putStrLn $ "tensorOfMaps lhs == rhs: " ++ show (lhs2 == rhs2)

  putStrLn $ "site kron arr basis: skipped"

  let mfS = extract (getLM sf)
      mgS = extract (getLM sid)
      inpS = HM.fromList $ VS.toList (toArray (sx ⊗ sy) :: VS.Vector ℂ)
      outS = HM.fromList $ VS.toList (toArray rhs2 :: VS.Vector ℂ)
      afS = HM.tr' mfS
      agS = HM.tr' mgS
  putStrLn $ "site mf dims: " ++ show (HM.size mfS)
  mapM_ (\(name, op) -> putStrLn $ name ++ ": " ++ show (HM.norm_2 (op HM.#> inpS - outS) < 1e-10)) $
    [ ("kron(agS,afS)", HM.kronecker agS afS)
    , ("kron(afS,agS)", HM.kronecker afS agS)
    ]

getLM :: forall a b. (KnownNat (Dimension a), KnownNat (Dimension b))
      => (a +> b) -> M (Dimension b) (Dimension a)
getLM (LinearMap m) = unsafeCoerce m

tensorMat :: forall n w. (KnownNat n, KnownNat (Dimension w)) => C n ⊗ w -> M (Dimension w) n
tensorMat (Tensor t) = unsafeCoerce t

stepIO :: String -> IO a -> IO ()
stepIO name action =
  try action >>= printStep name
  where
    printStep :: String -> Either SomeException a -> IO ()
    printStep n (Left e) = putStrLn $ "FAIL " ++ n ++ ": " ++ show e
    printStep n Right{} = putStrLn $ "OK   " ++ n

step :: Show a => String -> a -> IO ()
step name action =
  try (evaluate action) >>= printStep name
  where
    printStep :: Show b => String -> Either SomeException b -> IO ()
    printStep n (Left e) = putStrLn $ "FAIL " ++ n ++ ": " ++ show e
    printStep n (Right v) = putStrLn $ "OK   " ++ n ++ ": " ++ show v
