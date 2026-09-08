{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

-- | SU(3) representation category as 'FusionTheory' \/ 'FusionData'.
--
-- Irreps are Dynkin labels @(p, q)@. Term-level @TermLab = (Int, Int)@.
-- Fusion multiplicities are Littlewood–Richardson coefficients (can be @> 1@,
-- e.g. @N_{(1,1)(1,1)}^{(1,1)} = 2@ in @8 ⊗ 8@).
--
-- Type-level @FuseN@ is only filled for unitors; general type-level fusion is
-- not implemented (use 'su3FuseOutcomes'). @fSymbol@ is stubbed; @rSymbol@ is
-- the symmetric-category flip sign on multiplicity-free channels.
module Experiments.Fusion.SU3
  ( SU3Th
  , SU3Lab (..)
  , su3Dim
  , su3Mult
  , su3FuseOutcomes
  , su3RPhase
  ) where

import Data.Complex (Complex (..))
import Data.List (sortOn)
import GHC.TypeLits (Nat, TypeError, ErrorMessage (..))
import Experiments.Fusion.Data (FusionData (..))
import Experiments.Fusion.Theory (FusionTheory (..))

data SU3Th

-- | Type-level Dynkin label @(p, q)@.
data SU3Lab = SU3L Nat Nat

instance FusionTheory SU3Lab SU3Th where
  type UnitLab SU3Th = 'SU3L 0 0
  type FuseN SU3Th a b = SU3FuseN a b
  type DualLab SU3Th ('SU3L p q) = 'SU3L q p

-- | Unitors only — general SU(3) @FuseN@ needs type-level LR.
type family SU3FuseN (a :: SU3Lab) (b :: SU3Lab) :: [(SU3Lab, Nat)] where
  SU3FuseN ('SU3L 0 0) b = '[ '(b, 1)]
  SU3FuseN a ('SU3L 0 0) = '[ '(a, 1)]
  SU3FuseN a b =
    TypeError
      ( 'Text "SU(3) FuseN is only defined for unitors; use su3FuseOutcomes / FusionData at term level for "
          ':<>: 'ShowType a
          ':<>: 'Text " ⊗ "
          ':<>: 'ShowType b
      )

--------------------------------------------------------------------------------
-- Dimensions \/ Young size
--------------------------------------------------------------------------------

-- | @dim(p,q) = (p+1)(q+1)(p+q+2)/2@.
su3Dim :: (Int, Int) -> Int
su3Dim (p, q) = (p + 1) * (q + 1) * (p + q + 2) `div` 2

-- | Number of boxes in the @(p,q)@ Young diagram @(p+q,q)@.
su3Size :: (Int, Int) -> Int
su3Size (p, q) = p + 2 * q

--------------------------------------------------------------------------------
-- Littlewood–Richardson (length ≤ 3) → SU(3) multiplicity
--------------------------------------------------------------------------------

type Part = [Int]

pad3 :: Part -> Part
pad3 xs = take 3 (xs ++ [0, 0, 0])

dynkinPart :: (Int, Int) -> Part
dynkinPart (p, q) = [p + q, q, 0]

-- | Outer multiplicity of @(p,q)@ in @(p1,q1) ⊗ (p2,q2)@.
su3Mult :: (Int, Int) -> (Int, Int) -> (Int, Int) -> Int
su3Mult a b c
  | any (< 0) [fst a, snd a, fst b, snd b, fst c, snd c] = 0
  | r < 0 || r `mod` 3 /= 0 = 0
  | otherwise =
      let k = r `div` 3
          (p, q) = c
          nu = [p + q + k, q + k, k]
       in lrCoefficient (dynkinPart a) (dynkinPart b) nu
  where
    r = su3Size a + su3Size b - su3Size c

-- | @c^ν_{λμ}@ for partitions of length ≤ 3 (Yamanouchi SSYT count).
lrCoefficient :: Part -> Part -> Part -> Int
lrCoefficient lambda mu nu
  | sum nu' /= sum lambda' + sum mu' = 0
  | or (zipWith (<) nu' lambda') = 0
  | otherwise = countLR (skewBoxes nu' lambda') (contentFromMu mu') []
  where
    lambda' = pad3 lambda
    mu' = pad3 mu
    nu' = pad3 nu

contentFromMu :: Part -> [Int]
contentFromMu [m1, m2, m3] =
  replicate m1 1 ++ replicate m2 2 ++ replicate m3 3
contentFromMu _ = error "contentFromMu: expected length-3 partition"

skewBoxes :: Part -> Part -> [(Int, Int)]
skewBoxes nu la =
  [ (r, c)
  | r <- [0 .. 2]
  , c <- [la !! r .. nu !! r - 1]
  ]

-- | Backtracking fill of skew boxes in row-major order with a fixed multiset
-- of entries; SSYT constraints online, Yamanouchi on the English reading word
-- at completion (each row right-to-left, rows top-to-bottom).
countLR
  :: [(Int, Int)] -- remaining boxes (row, col)
  -> [Int] -- remaining letters (multiset)
  -> [((Int, Int), Int)] -- placed cells
  -> Int
countLR [] [] placed =
  if yamanouchiWord placed then 1 else 0
countLR [] _ _ = 0
countLR _ [] _ = 0
countLR ((r, c) : boxes) letters placed =
  sum
    [ countLR boxes (delete1 x letters) (((r, c), x) : placed)
    | x <- uniq letters
    , rowOk r c x placed
    , colOk r c x placed
    ]

delete1 :: Int -> [Int] -> [Int]
delete1 _ [] = []
delete1 x (y : ys)
  | x == y = ys
  | otherwise = y : delete1 x ys

uniq :: [Int] -> [Int]
uniq = go []
  where
    go acc [] = reverse acc
    go acc (x : xs)
      | x `elem` acc = go acc xs
      | otherwise = go (x : acc) xs

yamanouchiWord :: [((Int, Int), Int)] -> Bool
yamanouchiWord placed =
  go (0, 0, 0) (readingWord placed)
  where
    go _ [] = True
    go counts (x : xs) =
      let counts' = bump x counts
       in yamanouchi counts' && go counts' xs

readingWord :: [((Int, Int), Int)] -> [Int]
readingWord placed =
  [ x
  | r <- [0 .. 2]
  , let cols = [ (c, x) | ((r', c), x) <- placed, r' == r ]
  , (_, x) <- reverse (sortOn fst cols)
  ]

bump :: Int -> (Int, Int, Int) -> (Int, Int, Int)
bump 1 (a, b, c) = (a + 1, b, c)
bump 2 (a, b, c) = (a, b + 1, c)
bump 3 (a, b, c) = (a, b, c + 1)
bump _ _ = error "bump: letter out of range"

yamanouchi :: (Int, Int, Int) -> Bool
yamanouchi (n1, n2, n3) = n1 >= n2 && n2 >= n3

rowOk :: Int -> Int -> Int -> [((Int, Int), Int)] -> Bool
rowOk r c x placed =
  case lookup (r, c - 1) placed of
    Nothing -> True
    Just y -> y <= x

colOk :: Int -> Int -> Int -> [((Int, Int), Int)] -> Bool
colOk r c x placed =
  case lookup (r - 1, c) placed of
    Nothing -> True
    Just y -> y < x

--------------------------------------------------------------------------------
-- Fusion list \/ R-phase
--------------------------------------------------------------------------------

su3FuseOutcomes :: (Int, Int) -> (Int, Int) -> [((Int, Int), Int)]
su3FuseOutcomes a b =
  let s = su3Size a + su3Size b
      -- Generous dominant-weight bound.
      hi = s
   in [ ((p, q), m)
      | p <- [0 .. hi]
      , q <- [0 .. hi]
      , p + 2 * q <= s
      , (s - (p + 2 * q)) `mod` 3 == 0
      , let m = su3Mult a b (p, q)
      , m > 0
      ]

-- | Flip sign on a multiplicity-free channel: @(-1)^{(|a|+|b|-|c|)/2}@.
-- Invalid for @N>1@ (needs a matrix on the multiplicity space).
su3RPhase :: (Int, Int) -> (Int, Int) -> (Int, Int) -> Complex Double
su3RPhase a b c
  | odd diff = error "su3RPhase: size difference must be even"
  | even (diff `div` 2) = 1
  | otherwise = -1
  where
    diff = su3Size a + su3Size b - su3Size c

instance FusionData SU3Lab SU3Th where
  type TermLab SU3Th = (Int, Int)
  fuseOutcomes _ = su3FuseOutcomes
  nSymbol _ a b c = su3Mult a b c
  fSymbol _ _inv _a _b _c _d _e =
    error "Experiments.Fusion.SU3: fSymbol stub — SU(3) 6j / F-symbols not wired"
  rSymbol p a b c =
    case nSymbol p a b c of
      0 -> 0
      1 -> su3RPhase a b c
      _ ->
        error "Experiments.Fusion.SU3: rSymbol for N>1 needs a multiplicity matrix"
  cupCoeff _ pq = fromIntegral (su3Dim pq) :+ 0
