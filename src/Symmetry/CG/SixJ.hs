{-# LANGUAGE BangPatterns #-}

-- | Wigner 6j symbols and SU(2) F-amplitudes on @2j@ ('tj') labels.
--
-- Convention (matches CG densify Schur blocks):
--
-- @
-- [F^{a b c}_d]_{e f}
--   = (-1)^{(a+b+c+d)/2} √((e+1)(f+1)) {a/2 b/2 e/2 ; c/2 d/2 f/2}
-- @
--
-- with all of @a,b,c,d,e,f :: Int@ as twice-spin. Real orthogonal:
-- @[F^{-1}]_{e f} = [F]_{f e}@.
module Symmetry.CG.SixJ
  ( wigner6jTJ
  , su2FAmpTJ
  , triangleTJ
  ) where

import Data.Complex (Complex (..))

-- | Factorial on @n >= 0@; @n < 0@ → @0@ (invalid Racah term).
fac :: Int -> Double
fac n
  | n < 0 = 0
  | otherwise = fromIntegral (go 1 n)
  where
    go !acc 0 = acc
    go !acc k = go (acc * k) (k - 1)

-- | Triangle inequalities on @2j@ labels (+ parity).
triangleTJ :: Int -> Int -> Int -> Bool
triangleTJ a b c =
  a >= 0
    && b >= 0
    && c >= 0
    && a + b >= c
    && a + c >= b
    && b + c >= a
    && even (a + b + c)

-- | @Δ(j1,j2,j3)@ with arguments as @2j@.
deltaTJ :: Int -> Int -> Int -> Double
deltaTJ a b c
  | not (triangleTJ a b c) = 0
  | otherwise =
      let x = (a + b - c) `div` 2
          y = (a - b + c) `div` 2
          z = (-a + b + c) `div` 2
          n = (a + b + c) `div` 2 + 1
       in sqrt (fac x * fac y * fac z / fac n)

-- | Wigner 6j @{j1 j2 j3 ; j4 j5 j6}@ with all arguments as @2j@.
wigner6jTJ :: Int -> Int -> Int -> Int -> Int -> Int -> Double
wigner6jTJ j1 j2 j3 j4 j5 j6
  | not
      ( triangleTJ j1 j2 j3
          && triangleTJ j1 j5 j6
          && triangleTJ j4 j2 j6
          && triangleTJ j4 j5 j3
      ) =
      0
  | otherwise =
      let tri =
            deltaTJ j1 j2 j3
              * deltaTJ j1 j5 j6
              * deltaTJ j4 j2 j6
              * deltaTJ j4 j5 j3
          -- Summation index as 2t (even steps).
          tMin =
            maximum
              [ j1 + j2 + j3
              , j1 + j5 + j6
              , j4 + j2 + j6
              , j4 + j5 + j3
              ]
          tMax =
            minimum
              [ j1 + j2 + j4 + j5
              , j2 + j3 + j5 + j6
              , j3 + j1 + j6 + j4
              ]
          terms =
            [ let t2 = t
                  -- t = t2/2; (t+1)! = (t2/2 + 1)!
                  num = ((-1) ^ (t2 `div` 2)) * fac (t2 `div` 2 + 1)
                  den =
                    fac ((t2 - j1 - j2 - j3) `div` 2)
                      * fac ((t2 - j1 - j5 - j6) `div` 2)
                      * fac ((t2 - j4 - j2 - j6) `div` 2)
                      * fac ((t2 - j4 - j5 - j3) `div` 2)
                      * fac ((j1 + j2 + j4 + j5 - t2) `div` 2)
                      * fac ((j2 + j3 + j5 + j6 - t2) `div` 2)
                      * fac ((j3 + j1 + j6 + j4 - t2) `div` 2)
               in num / den
            | t <- [tMin, tMin + 2 .. tMax]
            ]
       in tri * sum terms

-- | @[F^{a b c}_d]_{e f}@ on @2j@ labels (real).
su2FAmpTJ :: Int -> Int -> Int -> Int -> Int -> Int -> Complex Double
su2FAmpTJ a b c d e f
  | odd (a + b + c + d) = 0
  | not (triangleTJ a b e) = 0
  | not (triangleTJ e c d) = 0
  | not (triangleTJ b c f) = 0
  | not (triangleTJ a f d) = 0
  | otherwise =
      let phase = if even ((a + b + c + d) `div` 2) then 1 else -1
          -- 6j is {a/2 b/2 e/2 ; c/2 d/2 f/2}
          six = wigner6jTJ a b e c d f
          s = sqrt (fromIntegral ((e + 1) * (f + 1)))
       in (phase * s * six) :+ 0
