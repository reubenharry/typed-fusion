{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | SU(2) Clebsch–Gordan fuse: unfused product basis → fused multiplet layout.
--
-- Conventions (matching 'Symmetry.Group' / 'Symmetry.Tensor'):
--
--   * @tj@ is twice the spin; irrep dimension is @tj + 1@.
--   * Magnetic index @k = 0 .. tj@ corresponds to @tm = tj - 2k@ (highest weight first).
--   * Sector storage is multiplicity ⊗ irrep (mult slow, @m@ fast), matching
--     'Symmetry.HomBlock.su2ExpandBlock'.
--   * @C n ⊗ C m@ via 'toArray' uses second-factor-fastest: @i*m + j@.
--   * Fused output matches coalesced @'Tensor' SU2 r q@: sectors sorted by @tj@,
--     equal-@tj@ contributions merged into one multiplicity (CG walk order
--     within each @tj@).
--
-- Built by highest-weight + @J−@ (Condon–Shortley).
module Symmetry.CG.SU2
  ( fuseSU2Flat
  , cgMatrixTwoIrreps
  , fusionChannels
  , sectorsSU2
  , repDimOf
  ) where

import Control.Monad.ST (runST)
import Data.Complex (Complex (..))
import Data.Proxy (Proxy (..))
import Data.Singletons (fromSing)
import qualified Data.Map.Strict as Map
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Storable.Mutable as MVS
import GHC.TypeLits (natVal)
import Symmetry.Group (Group (SU2))
import Symmetry.RepSingleton (SRep (..))

-- | Total-@tj@ channels in @j1 ⊗ j2@ (same order as 'TensorIrrepRepSU2').
fusionChannels :: Int -> Int -> [Int]
fusionChannels j1 j2 = [lo, lo + 2 .. hi]
  where
    lo = abs (j1 - j2)
    hi = j1 + j2

tmOf :: Int -> Int -> Int
tmOf tj k = tj - 2 * k

-- | @⟨j, m−1| J− |j m⟩@ (@ħ = 1@, doubled quantum numbers).
jMinusCoeff :: Int -> Int -> Double
jMinusCoeff tj tm =
  0.5 * sqrt (fromIntegral ((tj + tm) * (tj - tm + 2)))

dot :: [Double] -> [Double] -> Double
dot a b = sum (zipWith (*) a b)

norm2 :: [Double] -> Double
norm2 v = dot v v

normalize :: [Double] -> [Double]
normalize v =
  let n = sqrt (norm2 v)
  in  if n < 1e-14
        then error "Symmetry.CG.SU2: cannot normalize null vector"
        else map (/ n) v

subtractProj :: [Double] -> [Double] -> [Double]
subtractProj v u =
  let c = dot v u
  in  zipWith (\x y -> x - c * y) v u

-- | Real CG matrix for @j1 ⊗ j2@: rows = fused (channels × m), cols = product
-- @(k1,k2)@ with @k2@ fastest. Orthonormal rows; size @D × D@.
cgMatrixTwoIrreps :: Int -> Int -> [[Double]]
cgMatrixTwoIrreps j1 j2 =
  let d1 = j1 + 1
      d2 = j2 + 1
      chans = fusionChannels j1 j2
  in  concatMap snd (buildMultiplets j1 j2 d1 d2 chans)
  where
    pidx d2' k1 k2 = k1 * d2' + k2

    basisVec d1' d2' k1 k2 =
      [ if i == pidx d2' k1 k2 then 1 else 0 | i <- [0 .. d1' * d2' - 1] ]

    -- Process high @tj@ first (Gram–Schmidt); @acc@ conses so low-@tj@ ends up first.
    buildMultiplets tj1 tj2 d1' d2' chans =
      snd (foldl step ([], []) (reverse chans))
      where
        step (higher, acc) tj =
          let hw0 = rawHighest tj1 tj2 d1' d2' tj
              hw = normalize (foldl subtractProj hw0 higher)
              tower = lowerTower tj1 tj2 d1' d2' tj hw
          in  (tower ++ higher, (tj, tower) : acc)

    rawHighest tj1 tj2 d1' d2' tj =
      let tm2 = tj - tj1
          k2 = (tj2 - tm2) `div` 2
      in  if tm2 >= -tj2 && tm2 <= tj2 && even (tj2 - tm2) && k2 >= 0 && k2 < d2'
            then basisVec d1' d2' 0 k2
            else
              head
                [ basisVec d1' d2' a b
                | a <- [0 .. d1' - 1]
                , b <- [0 .. d2' - 1]
                , tmOf tj1 a + tmOf tj2 b == tj
                ]

    applyJminus tj1 tj2 d1' d2' v =
      [ sum
          [ c
          | k1 <- [0 .. d1' - 1]
          , k2 <- [0 .. d2' - 1]
          , let amp = v !! pidx d2' k1 k2
                tm1 = tmOf tj1 k1
                tm2 = tmOf tj2 k2
          , (k1', k2', c) <-
              [ (k1 + 1, k2, amp * jMinusCoeff tj1 tm1) | k1 + 1 < d1' ]
                ++ [ (k1, k2 + 1, amp * jMinusCoeff tj2 tm2) | k2 + 1 < d2' ]
          , pidx d2' k1' k2' == i
          ]
      | i <- [0 .. d1' * d2' - 1]
      ]

    lowerTower tj1 tj2 d1' d2' tj hw = go tj hw
      where
        go tm v
          | tm < -tj = []
          | otherwise =
              let v' = normalize v
                  rest
                    | tm - 2 < -tj = []
                    | otherwise =
                        let c = jMinusCoeff tj tm
                            raw = applyJminus tj1 tj2 d1' d2' v'
                        in  if c < 1e-14 then [] else go (tm - 2) (map (/ c) raw)
              in  v' : rest

-- | @(tj, multiplicity, flat offset)@ for an SU(2) spine.
sectorsSU2 :: SRep SU2 r -> [(Int, Int, Int)]
sectorsSU2 = go 0
  where
    go :: Int -> SRep SU2 r0 -> [(Int, Int, Int)]
    go _ SRepNilSU2 = []
    go !off (SRepConsSU2 @j @m sj rest) =
      let tj = fromIntegral (fromSing sj)
          mult = fromIntegral (natVal (Proxy @m))
          stride = mult * (tj + 1)
      in  (tj, mult, off) : go (off + stride) rest

repDimOf :: [(Int, Int, Int)] -> Int
repDimOf [] = 0
repDimOf secs =
  let (tj, m, off) = last secs
  in  off + m * (tj + 1)

-- | Apply CG fuse on flat Kronecker buffers (@toArray@ layout).
-- Output layout matches coalesced @'Tensor' SU2@: sorted by @tj@, merged mult.
fuseSU2Flat
  :: SRep SU2 r
  -> SRep SU2 q
  -> VS.Vector (Complex Double)
  -> VS.Vector (Complex Double)
fuseSU2Flat sr sq vin =
  let secsR = sectorsSU2 sr
      secsQ = sectorsSU2 sq
      dimQ = repDimOf secsQ
      -- CG walk contributions (stable order within each output @tj@).
      contribs =
        [ (tjOut, m1 * m2, tj1, m1, off1, tj2, m2, off2)
        | (tj1, m1, off1) <- secsR
        , (tj2, m2, off2) <- secsQ
        , tjOut <- fusionChannels tj1 tj2
        ]
      multByJ =
        Map.fromListWith (+) [ (tj, dmult) | (tj, dmult, _, _, _, _, _, _) <- contribs ]
      sortedJs = Map.keys multByJ
      outOffByJ =
        Map.fromList $
          zip sortedJs (scanl (+) 0 [ m * (j + 1) | j <- sortedJs, let m = multByJ Map.! j ])
      dimF =
        case sortedJs of
          [] -> 0
          _ ->
            let j = last sortedJs
            in  (outOffByJ Map.! j) + (multByJ Map.! j) * (j + 1)
      -- Running multiplicity cursor per @tj@ (filled in contrib walk order).
      μ0ByJ = Map.fromList [ (j, 0) | j <- sortedJs ]
  in  runST $ do
        vout <- MVS.replicate dimF 0
        let writeContrib μCursors (tjOut, dmult, tj1, m1, off1, tj2, m2, off2) = do
              let d1 = tj1 + 1
                  d2 = tj2 + 1
                  mat = cgMatrixTwoIrreps tj1 tj2
                  chans = fusionChannels tj1 tj2
                  row0 = sum [ c + 1 | c <- takeWhile (/= tjOut) chans ]
                  nOut = tjOut + 1
                  μBase = μCursors Map.! tjOut
                  outOff0 = outOffByJ Map.! tjOut
              mapM_
                ( \(μ1, μ2) -> do
                    let μLocal = μ1 * m2 + μ2
                        μOut = μBase + μLocal
                        outBase = outOff0 + μOut * nOut
                    mapM_
                      ( \iOut -> do
                          let acc =
                                sum
                                  [ let col = k1 * d2 + k2
                                        iR = off1 + μ1 * d1 + k1
                                        iQ = off2 + μ2 * d2 + k2
                                        inp = vin VS.! (iR * dimQ + iQ)
                                        cg = (mat !! (row0 + iOut)) !! col
                                    in  inp * (cg :+ 0)
                                  | k1 <- [0 .. d1 - 1]
                                  , k2 <- [0 .. d2 - 1]
                                  ]
                          MVS.write vout (outBase + iOut) acc
                      )
                      [0 .. nOut - 1]
                )
                [ (μ1, μ2) | μ1 <- [0 .. m1 - 1], μ2 <- [0 .. m2 - 1] ]
              pure (Map.insert tjOut (μBase + dmult) μCursors)
        _ <- foldM writeContrib μ0ByJ contribs
        VS.freeze vout
  where
    foldM _ z [] = pure z
    foldM f z (x : xs) = do
      z' <- f z x
      foldM f z' xs
