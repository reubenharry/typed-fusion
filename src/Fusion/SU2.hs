{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}

-- | SU(2) representation category as 'FusionTheory' \/ 'FusionData'.
--
-- Type-level labels are @Nat@ (@2j@). Term-level @TermLab = Int@.
-- Spin fractions have kind 'SpinKind' (@1/2@, @3/2@, …); reduce with 'Spin' to a
-- @2j@ label (@Spin (1/2) = 1@, @Spin (1/1) = 2@).
-- @fSymbol@ is the screenshot amplitude @[F^{abc}_d]_{ef}@ (Racah \/ CG),
-- matching 'Symmetry.CG.FSymbol' Schur blocks for atom triples.
module Fusion.SU2
  ( SU2Th
  , SpinKind (..)
  , type (/)
  , Spin
  , su2FuseOutcomes
  , su2RPhase
  , su2FSymbol
  , allowedE
  , allowedF
  , fMultEntry
  , canFuseTJ
  , leftSectors
  , rightSectors
  , denseFAtoms
  , fmoveAtomsFlat
  , packAtomsFlat
  , unpackAtomsFlat
  ) where

import Control.Monad.ST (runST)
import Data.Complex (Complex (..))
import Data.List (elemIndex)
import Data.Maybe (fromMaybe, mapMaybe)
import Fusion.Data (FusionData (..))
import Fusion.Theory (FusionTheory (..))
import GHC.TypeLits (Nat, type (*), type Div)
import qualified Data.Map.Strict as Map
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Storable.Mutable as MVS
import qualified Numeric.LinearAlgebra as LA
import Symmetry.CG.SU2 (cgMatrixTwoIrreps, fusionChannels)
import Symmetry.Tensor (TensorIrrepRepSU2)

data SU2Th

-- | Spin @j = n/d@ (not a fusion label). Reduce with 'Spin' to @2j :: Nat@.
data SpinKind = Nat :/ Nat

-- | Build a 'SpinKind': @1/2@, @3/2@, @1/1@, …
type family (/) (n :: Nat) (d :: Nat) :: SpinKind where
  n / d = n ':/ d

infixl 7 /

-- | @j = n/d ↦ 2j@. Requires @d@ divides @2n@.
-- @Spin (1/2) = 1@, @Spin (1/1) = 2@, @Spin (3/2) = 3@.
type family Spin (s :: SpinKind) :: Nat where
  Spin (n :/ d) = Div (2 * n) d

instance FusionTheory Nat SU2Th where
  type UnitLab SU2Th = 0
  type FuseN SU2Th j1 j2 = TensorIrrepRepSU2 j1 j2
  type DualLab SU2Th j = j

su2FuseOutcomes :: Int -> Int -> [(Int, Int)]
su2FuseOutcomes j1 j2 =
  let lo = abs (j1 - j2)
      hi = j1 + j2
   in [ (j, 1) | j <- [lo, lo + 2 .. hi] ]

-- | Channel R-phase for bosonic SU(2): @(-1)^{j₁+j₂-j}@ with labels as @2j@.
-- Equivalent to the single-channel content of 'Symmetry.CG.RSymbol'.
su2RPhase :: Int -> Int -> Int -> Complex Double
su2RPhase tj1 tj2 tj
  | odd (tj1 + tj2 - tj) =
      error "su2RPhase: tj1+tj2-tj must be even (invalid fusion channel)"
  | even ((tj1 + tj2 - tj) `div` 2) = 1
  | otherwise = -1

--------------------------------------------------------------------------------
-- Term-level F-symbols (atom triples), CG-consistent with Symmetry.CG.FSymbol
--------------------------------------------------------------------------------

canFuseTJ :: Int -> Int -> Int -> Bool
canFuseTJ a b c =
  abs (a - b) <= c && c <= a + b && even (a + b - c)

-- | Left intermediates @e@ for @((a⊗b)e)⊗c → d@.
allowedE :: Int -> Int -> Int -> Int -> [Int]
allowedE a b c d =
  [ e
  | e <- fusionChannels a b
  , canFuseTJ e c d
  ]

-- | Right intermediates @f@ for @a⊗((b⊗c)f) → d@.
allowedF :: Int -> Int -> Int -> Int -> [Int]
allowedF a b c d =
  [ f
  | f <- fusionChannels b c
  , canFuseTJ a f d
  ]

-- | CG fuse of two atom irreps (@2j@ labels): product flat → fused flat
-- (channels in 'fusionChannels' order, each of dim @tj+1@).
applyCGAtoms :: Int -> Int -> VS.Vector (Complex Double) -> VS.Vector (Complex Double)
applyCGAtoms j1 j2 vin =
  let mat = cgMatrixTwoIrreps j1 j2
      nRows = length mat
      nCols = (j1 + 1) * (j2 + 1)
   in VS.generate nRows $ \r ->
        sum
          [ ((mat !! r !! col) :+ 0) * (vin VS.! col)
          | col <- [0 .. nCols - 1]
          ]

-- | Fuse coalesced left spine (unit-mult channels) with atom @c@.
fuseChannelsAtom
  :: [Int]
  -> Int
  -> VS.Vector (Complex Double)
  -> VS.Vector (Complex Double)
fuseChannelsAtom leftChans c vin =
  let dimC = c + 1
      leftOffs =
        scanl (+) 0 [tj + 1 | tj <- leftChans]
      dimL = last leftOffs
      contribs =
        [ (tjOut, e, eOff)
        | (e, eOff) <- zip leftChans leftOffs
        , tjOut <- fusionChannels e c
        ]
      multByJ =
        Map.fromListWith (+) [(tj, 1) | (tj, _, _) <- contribs]
      sortedJs = Map.keys multByJ
      outOffByJ =
        Map.fromList $
          zip
            sortedJs
            (scanl (+) 0 [m * (j + 1) | j <- sortedJs, let m = multByJ Map.! j])
      dimF =
        case sortedJs of
          [] -> 0
          _ ->
            let j = last sortedJs
             in (outOffByJ Map.! j) + (multByJ Map.! j) * (j + 1)
      μ0 = Map.fromList [(j, 0) | j <- sortedJs]
   in runST $ do
        vout <- MVS.replicate dimF 0
        let step μCursors (tjOut, e, eOff) = do
              let mat = cgMatrixTwoIrreps e c
                  chans = fusionChannels e c
                  row0 = sum [ch + 1 | ch <- takeWhile (/= tjOut) chans]
                  nOut = tjOut + 1
                  dE = e + 1
                  μBase = μCursors Map.! tjOut
                  outBase = (outOffByJ Map.! tjOut) + μBase * nOut
              mapM_
                ( \iOut -> do
                    let acc =
                          sum
                            [ let col = kE * dimC + kC
                                  inp = vin VS.! ((eOff + kE) * dimC + kC)
                                  cg = (mat !! (row0 + iOut)) !! col
                               in inp * (cg :+ 0)
                            | kE <- [0 .. dE - 1]
                            , kC <- [0 .. dimC - 1]
                            ]
                    MVS.write vout (outBase + iOut) acc
                )
                [0 .. nOut - 1]
              pure (Map.insert tjOut (μBase + 1) μCursors)
        _ <- foldM step μ0 contribs
        VS.freeze vout
  where
    foldM _ z [] = pure z
    foldM f z (x : xs) = do
      z' <- f z x
      foldM f z' xs

-- | @((a⊗b)⊗c)@ product → left-fused coalesced flat.
fuseLeftAtoms
  :: Int -> Int -> Int -> VS.Vector (Complex Double) -> VS.Vector (Complex Double)
fuseLeftAtoms a b c vin =
  let da = a + 1
      db = b + 1
      dc = c + 1
      dimAB = da * db
      dimABf = dimAB
      mid = runST $ do
        m <- MVS.new (dimABf * dc)
        mapM_
          ( \iC -> do
              let fiber =
                    VS.generate dimAB $ \iAB ->
                      vin VS.! (iAB * dc + iC)
                  fused = applyCGAtoms a b fiber
              mapM_
                ( \iAB' ->
                    MVS.write m (iAB' * dc + iC) (fused VS.! iAB')
                )
                [0 .. dimABf - 1]
          )
          [0 .. dc - 1]
        VS.freeze m
   in fuseChannelsAtom (fusionChannels a b) c mid

-- | @(a⊗(b⊗c))@ product → right-fused coalesced flat.
fuseRightAtoms
  :: Int -> Int -> Int -> VS.Vector (Complex Double) -> VS.Vector (Complex Double)
fuseRightAtoms a b c vin =
  let da = a + 1
      db = b + 1
      dc = c + 1
      dimBC = db * dc
      dimBCf = dimBC
      mid = runST $ do
        m <- MVS.new (da * dimBCf)
        mapM_
          ( \iA -> do
              let fiber =
                    VS.generate dimBC $ \iBC ->
                      vin VS.! (iA * dimBC + iBC)
                  fused = applyCGAtoms b c fiber
              mapM_
                ( \iBC' ->
                    MVS.write m (iA * dimBCf + iBC') (fused VS.! iBC')
                )
                [0 .. dimBCf - 1]
          )
          [0 .. da - 1]
        VS.freeze m
   in fuseAtomChannels a (fusionChannels b c) mid

-- | Fuse atom @a@ with coalesced right spine.
fuseAtomChannels
  :: Int
  -> [Int]
  -> VS.Vector (Complex Double)
  -> VS.Vector (Complex Double)
fuseAtomChannels a rightChans vin =
  let da = a + 1
      rightOffs = scanl (+) 0 [tj + 1 | tj <- rightChans]
      dimR = last rightOffs
      contribs =
        [ (tjOut, f, fOff)
        | (f, fOff) <- zip rightChans rightOffs
        , tjOut <- fusionChannels a f
        ]
      multByJ =
        Map.fromListWith (+) [(tj, 1) | (tj, _, _) <- contribs]
      sortedJs = Map.keys multByJ
      outOffByJ =
        Map.fromList $
          zip
            sortedJs
            (scanl (+) 0 [m * (j + 1) | j <- sortedJs, let m = multByJ Map.! j])
      dimF =
        case sortedJs of
          [] -> 0
          _ ->
            let j = last sortedJs
             in (outOffByJ Map.! j) + (multByJ Map.! j) * (j + 1)
      μ0 = Map.fromList [(j, 0) | j <- sortedJs]
   in runST $ do
        vout <- MVS.replicate dimF 0
        let step μCursors (tjOut, f, fOff) = do
              let mat = cgMatrixTwoIrreps a f
                  chans = fusionChannels a f
                  row0 = sum [ch + 1 | ch <- takeWhile (/= tjOut) chans]
                  nOut = tjOut + 1
                  dF = f + 1
                  μBase = μCursors Map.! tjOut
                  outBase = (outOffByJ Map.! tjOut) + μBase * nOut
              mapM_
                ( \iOut -> do
                    let acc =
                          sum
                            [ let col = kA * dF + kF
                                  inp = vin VS.! (kA * dimR + (fOff + kF))
                                  cg = (mat !! (row0 + iOut)) !! col
                               in inp * (cg :+ 0)
                            | kA <- [0 .. da - 1]
                            , kF <- [0 .. dF - 1]
                            ]
                    MVS.write vout (outBase + iOut) acc
                )
                [0 .. nOut - 1]
              pure (Map.insert tjOut (μBase + 1) μCursors)
        _ <- foldM step μ0 contribs
        VS.freeze vout
  where
    foldM _ z [] = pure z
    foldM f z (x : xs) = do
      z' <- f z x
      foldM f z' xs

matFromMap
  :: Int
  -> Int
  -> (VS.Vector (Complex Double) -> VS.Vector (Complex Double))
  -> LA.Matrix (Complex Double)
matFromMap _nRows nCols f =
  LA.fromColumns
    [ VS.convert (f (e i))
    | i <- [0 .. nCols - 1]
    ]
  where
    e i = VS.generate nCols $ \j -> if i == j then 1 else 0

-- | Dense left→right F for atom triple (same construction as 'denseFMove').
denseFAtoms :: Int -> Int -> Int -> LA.Matrix (Complex Double)
denseFAtoms a b c =
  let dimP = (a + 1) * (b + 1) * (c + 1)
      zeroP = VS.replicate dimP 0
      nL = VS.length (fuseLeftAtoms a b c zeroP)
      nR = VS.length (fuseRightAtoms a b c zeroP)
      mL = matFromMap nL dimP (fuseLeftAtoms a b c)
      mR = matFromMap nR dimP (fuseRightAtoms a b c)
   in mR LA.<> LA.tr mL

-- | Apply dense F (or @Fᵀ ≈ F⁻¹@) on left\/right sector flats from
-- 'leftSectors' \/ 'rightSectors'. Label-driven — no per-triple typed flats.
fmoveAtomsFlat
  :: Bool
  -> Int
  -> Int
  -> Int
  -> VS.Vector (Complex Double)
  -> VS.Vector (Complex Double)
fmoveAtomsFlat inv a b c vin =
  let mat = denseFAtoms a b c
      v = VS.convert vin :: LA.Vector (Complex Double)
      v' =
        if inv
          then LA.tr mat LA.#> v
          else mat LA.#> v
   in VS.convert v'

-- | Sector layout of left-fused @((a⊗b)⊗c)@: @(tj, mult, flat offset)@.
leftSectors :: Int -> Int -> Int -> [(Int, Int, Int)]
leftSectors a b c =
  let es = fusionChannels a b
      contribs =
        [ tjOut
        | e <- es
        , tjOut <- fusionChannels e c
        ]
      multByJ = Map.fromListWith (+) [(tj, 1) | tj <- contribs]
      sortedJs = Map.keys multByJ
      offs =
        scanl (+) 0 [m * (j + 1) | j <- sortedJs, let m = multByJ Map.! j]
   in zip3 sortedJs [multByJ Map.! j | j <- sortedJs] offs

rightSectors :: Int -> Int -> Int -> [(Int, Int, Int)]
rightSectors a b c =
  let fs = fusionChannels b c
      contribs =
        [ tjOut
        | f <- fs
        , tjOut <- fusionChannels a f
        ]
      multByJ = Map.fromListWith (+) [(tj, 1) | tj <- contribs]
      sortedJs = Map.keys multByJ
      offs =
        scanl (+) 0 [m * (j + 1) | j <- sortedJs, let m = multByJ Map.! j]
   in zip3 sortedJs [multByJ Map.! j | j <- sortedJs] offs

-- | Pack @(d, mid, irrep)@ channels into a left\/right sector flat.
packAtomsFlat
  :: [(Int, Int, Int)]
  -> (Int -> [Int])
  -> [(Int, Int, VS.Vector (Complex Double))]
  -> VS.Vector (Complex Double)
packAtomsFlat secs midsOf chans =
  let total =
        case secs of
          [] -> 0
          _ ->
            let (d, m, off) = last secs
             in off + m * (d + 1)
      byKey = Map.fromList [((d, mid), v) | (d, mid, v) <- chans]
   in VS.create $ do
        vout <- MVS.new total
        MVS.set vout 0
        mapM_
          ( \(d, _mult, off) ->
              let dim = d + 1
                  mids = midsOf d
               in mapM_
                    ( \(ei, mid) ->
                        case Map.lookup (d, mid) byKey of
                          Nothing -> pure ()
                          Just vec ->
                            mapM_
                              ( \i ->
                                  MVS.write
                                    vout
                                    (off + ei * dim + i)
                                    (vec VS.! i)
                              )
                              [0 .. dim - 1]
                    )
                    (zip [0 :: Int ..] mids)
          )
          secs
        pure vout

-- | Inverse of 'packAtomsFlat'.
unpackAtomsFlat
  :: [(Int, Int, Int)]
  -> (Int -> [Int])
  -> VS.Vector (Complex Double)
  -> [(Int, Int, VS.Vector (Complex Double))]
unpackAtomsFlat secs midsOf buf =
  [ (d, mid, VS.slice (off + ei * dim) dim buf)
  | (d, _mult, off) <- secs
  , let dim = d + 1
        mids = midsOf d
  , (ei, mid) <- zip [0 :: Int ..] mids
  ]

-- | Multiplicity-block entry @M_{f e} = [F^{abc}_d]_{ef}@ from dense F
-- (rows = right intermediate @f@, cols = left @e@; Schur expands as @⊗ I_{d+1}@).
fMultEntry
  :: Int -> Int -> Int -> Int -> Int -> Int -> Complex Double
fMultEntry a b c d e f =
  let mat = denseFAtoms a b c
      es = allowedE a b c d
      fs = allowedF a b c d
      eIdx = fromMaybe (-1) (elemIndex e es)
      fIdx = fromMaybe (-1) (elemIndex f fs)
      secsL = leftSectors a b c
      secsR = rightSectors a b c
   in case (lookup3 d secsL, lookup3 d secsR, eIdx >= 0 && fIdx >= 0) of
        (Just (_mL, offL), Just (_mR, offR), True) ->
          let dimD = d + 1
              row = offR + fIdx * dimD
              col = offL + eIdx * dimD
           in mat `LA.atIndex` (row, col)
        _ -> 0
  where
    lookup3 tj secs =
      case [ (m, off) | (t, m, off) <- secs, t == tj ] of
        (p : _) -> Just p
        [] -> Nothing

-- | Screenshot F-symbol: @|(ab)e;c;d⟩ = Σ_f [F^{abc}_d]_{ef} |a;(bc)f;d⟩@.
-- Labels are @2j@. Returns @[(f, [F^{abc}_d]_{ef})]@. @inv@ yields @[F^{-1}]_{ef} = [F]_{fe}@.
su2FSymbol
  :: Bool
  -> Int
  -> Int
  -> Int
  -> Int
  -> Int
  -> [(Int, Complex Double)]
su2FSymbol inv a b c d e
  | not (canFuseTJ a b e) = []
  | not (canFuseTJ e c d) = []
  | otherwise =
      mapMaybe
        ( \f ->
            let amp =
                  if inv
                    then fMultEntry a b c d f e
                    else fMultEntry a b c d e f
             in if LA.magnitude amp < 1e-14
                  then Nothing
                  else Just (f, amp)
        )
        (allowedF a b c d)

instance FusionData Nat SU2Th where
  type TermLab SU2Th = Int
  fuseOutcomes _ = su2FuseOutcomes
  fSymbol _ = su2FSymbol
  rSymbol p a b c
    | nSymbol p a b c == 0 = 0
    | otherwise = su2RPhase a b c
  cupCoeff _ tj = fromIntegral (tj + 1) :+ 0
