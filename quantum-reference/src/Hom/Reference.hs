{-# LANGUAGE BangPatterns #-}

-- | Quarantined CG densify oracles for SU(2) F.
--
-- Production Hom F-moves use closed-form @fSymbol@ ('Symmetry.CG.SixJ.su2FAmpTJ')
-- via 'Fusion.SU2.fmoveChannels'. This module is the only home of dynamic
-- hmatrix densify (@denseFMoveSectors@, @fmoveFlatSectors@, @fMultBlock@).
--
-- Do **not** import this from production modules. Depend on the
-- @quantum-reference@ package from tests \/ probes only.
module Hom.Reference
  ( denseFMoveSectors
  , fmoveFlatSectors
  , fMultBlock
  , fuseTreeLeftSectors
  , fuseTreeRightSectors
  ) where

import Data.Complex (Complex (..))
import Control.Monad.ST (runST)
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Storable.Mutable as MVS
import qualified Numeric.LinearAlgebra as LA
import Symmetry.CG.SU2
  ( fuseSU2FlatSectors
  , fusedSectorPairs
  , repDimOf
  , sectorsFromPairs
  )

-- | @((r⊗q)⊗s)@ product flat → left-fused coalesced flat (sector lists).
fuseTreeLeftSectors
  :: [(Int, Int, Int)]
  -> [(Int, Int, Int)]
  -> [(Int, Int, Int)]
  -> VS.Vector (Complex Double)
  -> VS.Vector (Complex Double)
fuseTreeLeftSectors secsR secsQ secsS vin =
  let dr = repDimOf secsR
      dq = repDimOf secsQ
      ds = repDimOf secsS
      dimRQ = dr * dq
      secsRQ =
        sectorsFromPairs
          (fusedSectorPairs (pairsOf secsR) (pairsOf secsQ))
      dimRqF = repDimOf secsRQ
      mid = runST $ do
        m <- MVS.new (dimRqF * ds)
        mapM_
          ( \iS -> do
              let fiber =
                    VS.generate dimRQ $ \iRq ->
                      vin VS.! (iRq * ds + iS)
                  fused = fuseSU2FlatSectors secsR secsQ fiber
              mapM_
                ( \iRq' ->
                    MVS.write m (iRq' * ds + iS) (fused VS.! iRq')
                )
                [0 .. dimRqF - 1]
          )
          [0 .. ds - 1]
        VS.freeze m
   in fuseSU2FlatSectors secsRQ secsS mid
  where
    pairsOf secs = [(tj, m) | (tj, m, _) <- secs]

-- | @(r⊗(q⊗s))@ product flat → right-fused coalesced flat (sector lists).
fuseTreeRightSectors
  :: [(Int, Int, Int)]
  -> [(Int, Int, Int)]
  -> [(Int, Int, Int)]
  -> VS.Vector (Complex Double)
  -> VS.Vector (Complex Double)
fuseTreeRightSectors secsR secsQ secsS vin =
  let dr = repDimOf secsR
      dq = repDimOf secsQ
      ds = repDimOf secsS
      dimQS = dq * ds
      secsQS =
        sectorsFromPairs
          (fusedSectorPairs (pairsOf secsQ) (pairsOf secsS))
      dimQsF = repDimOf secsQS
      mid = runST $ do
        m <- MVS.new (dr * dimQsF)
        mapM_
          ( \iR -> do
              let fiber =
                    VS.generate dimQS $ \iQs ->
                      vin VS.! (iR * dimQS + iQs)
                  fused = fuseSU2FlatSectors secsQ secsS fiber
              mapM_
                ( \iQs' ->
                    MVS.write m (iR * dimQsF + iQs') (fused VS.! iQs')
                )
                [0 .. dimQsF - 1]
          )
          [0 .. dr - 1]
        VS.freeze m
   in fuseSU2FlatSectors secsR secsQS mid
  where
    pairsOf secs = [(tj, m) | (tj, m, _) <- secs]

matFromMapSecs
  :: Int
  -> Int
  -> (VS.Vector (Complex Double) -> VS.Vector (Complex Double))
  -> LA.Matrix (Complex Double)
matFromMapSecs _nRows nCols f =
  LA.fromColumns
    [ VS.convert (f (e i))
    | i <- [0 .. nCols - 1]
    ]
  where
    e i = VS.generate nCols $ \j -> if i == j then 1 else 0

-- | Dense left→right F for sector spines @r⊗q⊗s@ (@mR ∘ mL†@).
denseFMoveSectors
  :: [(Int, Int, Int)]
  -> [(Int, Int, Int)]
  -> [(Int, Int, Int)]
  -> LA.Matrix (Complex Double)
denseFMoveSectors secsR secsQ secsS =
  let dr = repDimOf secsR
      dq = repDimOf secsQ
      ds = repDimOf secsS
      dimP = dr * dq * ds
      secsRQ =
        sectorsFromPairs
          (fusedSectorPairs (pairsOf secsR) (pairsOf secsQ))
      secsQS =
        sectorsFromPairs
          (fusedSectorPairs (pairsOf secsQ) (pairsOf secsS))
      secsL =
        sectorsFromPairs
          (fusedSectorPairs (pairsOf secsRQ) (pairsOf secsS))
      secsRight =
        sectorsFromPairs
          (fusedSectorPairs (pairsOf secsR) (pairsOf secsQS))
      dimL = repDimOf secsL
      dimRight = repDimOf secsRight
      mL = matFromMapSecs dimL dimP (fuseTreeLeftSectors secsR secsQ secsS)
      mR = matFromMapSecs dimRight dimP (fuseTreeRightSectors secsR secsQ secsS)
   in mR LA.<> LA.tr mL
  where
    pairsOf secs = [(tj, m) | (tj, m, _) <- secs]

-- | Apply dense F (or @Fᵀ ≈ F⁻¹@) on left\/right coalesced flats of @r⊗q⊗s@.
fmoveFlatSectors
  :: Bool
  -> [(Int, Int, Int)]
  -> [(Int, Int, Int)]
  -> [(Int, Int, Int)]
  -> VS.Vector (Complex Double)
  -> VS.Vector (Complex Double)
fmoveFlatSectors inv secsR secsQ secsS vin =
  let mat = denseFMoveSectors secsR secsQ secsS
      v = VS.convert vin :: LA.Vector (Complex Double)
      v' =
        if inv
          then LA.tr mat LA.#> v
          else mat LA.#> v
   in VS.convert v'

-- | Multiplicity F-block @[F^{abc}_d]_{f e}@ (rows = right mids @f@, cols = left @e@).
-- Sampled from CG densify (Schur diagonal of @F ⊗ I_{d+1}@).
fMultBlock
  :: Int
  -> Int
  -> Int
  -> Int
  -> [Int]
  -> [Int]
  -> [[Complex Double]]
fMultBlock a b c d es fs =
  let secsA = sectorsFromPairs [(a, 1)]
      secsB = sectorsFromPairs [(b, 1)]
      secsC = sectorsFromPairs [(c, 1)]
      mat = denseFMoveSectors secsA secsB secsC
      ab = fusedSectorPairs [(a, 1)] [(b, 1)]
      secsL = sectorsFromPairs (fusedSectorPairs ab [(c, 1)])
      bc = fusedSectorPairs [(b, 1)] [(c, 1)]
      secsR = sectorsFromPairs (fusedSectorPairs [(a, 1)] bc)
      dimD = d + 1
      lookupOff tj secs =
        case [(m, off) | (t, m, off) <- secs, t == tj] of
          (p : _) -> Just p
          [] -> Nothing
   in case (lookupOff d secsL, lookupOff d secsR) of
        (Just (_mL, offL), Just (_mR, offR)) ->
          [ [ mat `LA.atIndex` (offR + fIdx * dimD, offL + eIdx * dimD)
            | eIdx <- [0 .. length es - 1]
            ]
          | fIdx <- [0 .. length fs - 1]
          ]
        _ ->
          replicate (length fs) (replicate (length es) 0)
