{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
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
-- matching 'Symmetry.CG.FSymbol' Schur blocks for irrep triples.
--
-- Flat CG \/ F-move on irrep triples delegates to 'Symmetry.CG.SU2'
-- (@fmoveFlatSectors@, @denseFMoveSectors@, …) with unit-mult spines.
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
  , denseFIrreps
  , fmoveIrrepsFlat
  , packIrrepsFlat
  , unpackIrrepsFlat
  ) where

import Data.Complex (Complex (..))
import Data.List (elemIndex)
import Data.Maybe (fromMaybe, mapMaybe)
import Fusion.Data (FusionData (..), allowedLeftMids, allowedRightMids)
import Fusion.Theory (FusionTheory (..))
import GHC.TypeLits (Nat, type (*), type Div)
import Data.Proxy (Proxy (..))
import qualified Data.Map.Strict as Map
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Storable.Mutable as MVS
import qualified Numeric.LinearAlgebra as LA
import Symmetry.CG.SU2
  ( denseFMoveSectors
  , fmoveFlatSectors
  , fusedSectorPairs
  , fusionChannels
  , sectorsFromPairs
  )
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
su2FuseOutcomes j1 j2 = [(j, 1) | j <- fusionChannels j1 j2]

-- | Channel R-phase for bosonic SU(2): @(-1)^{j₁+j₂-j}@ with labels as @2j@.
-- Equivalent to the single-channel content of 'Symmetry.CG.RSymbol'.
su2RPhase :: Int -> Int -> Int -> Complex Double
su2RPhase tj1 tj2 tj
  | odd (tj1 + tj2 - tj) =
      error "su2RPhase: tj1+tj2-tj must be even (invalid fusion channel)"
  | even ((tj1 + tj2 - tj) `div` 2) = 1
  | otherwise = -1

--------------------------------------------------------------------------------
-- Term-level F-symbols (irrep triples), CG-consistent with Symmetry.CG.FSymbol
--------------------------------------------------------------------------------

canFuseTJ :: Int -> Int -> Int -> Bool
canFuseTJ a b c = canFuseD (Proxy @SU2Th) a b c

-- | Left intermediates @e@ for @((a⊗b)e)⊗c → d@.
allowedE :: Int -> Int -> Int -> Int -> [Int]
allowedE = allowedLeftMids (Proxy @SU2Th)

-- | Right intermediates @f@ for @a⊗((b⊗c)f) → d@.
allowedF :: Int -> Int -> Int -> Int -> [Int]
allowedF = allowedRightMids (Proxy @SU2Th)

-- | Unit-multiplicity irrep spine for 'Symmetry.CG.SU2' sector APIs.
irrepSpine :: Int -> [(Int, Int, Int)]
irrepSpine tj = sectorsFromPairs [(tj, 1)]

-- | Dense left→right F for an irrep triple (@2j@ labels).
denseFIrreps :: Int -> Int -> Int -> LA.Matrix (Complex Double)
denseFIrreps a b c =
  denseFMoveSectors (irrepSpine a) (irrepSpine b) (irrepSpine c)

-- | Apply dense F (or @Fᵀ ≈ F⁻¹@) on left\/right sector flats from
-- 'leftSectors' \/ 'rightSectors'. Label-driven — no per-triple typed flats.
fmoveIrrepsFlat
  :: Bool
  -> Int
  -> Int
  -> Int
  -> VS.Vector (Complex Double)
  -> VS.Vector (Complex Double)
fmoveIrrepsFlat inv a b c =
  fmoveFlatSectors inv (irrepSpine a) (irrepSpine b) (irrepSpine c)

-- | Sector layout of left-fused @((a⊗b)⊗c)@: @(tj, mult, flat offset)@.
leftSectors :: Int -> Int -> Int -> [(Int, Int, Int)]
leftSectors a b c =
  let ab = fusedSectorPairs [(a, 1)] [(b, 1)]
   in sectorsFromPairs (fusedSectorPairs ab [(c, 1)])

rightSectors :: Int -> Int -> Int -> [(Int, Int, Int)]
rightSectors a b c =
  let bc = fusedSectorPairs [(b, 1)] [(c, 1)]
   in sectorsFromPairs (fusedSectorPairs [(a, 1)] bc)

-- | Pack @(d, mid, irrep)@ channels into a left\/right sector flat.
packIrrepsFlat
  :: [(Int, Int, Int)]
  -> (Int -> [Int])
  -> [(Int, Int, VS.Vector (Complex Double))]
  -> VS.Vector (Complex Double)
packIrrepsFlat secs midsOf chans =
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

-- | Inverse of 'packIrrepsFlat'.
unpackIrrepsFlat
  :: [(Int, Int, Int)]
  -> (Int -> [Int])
  -> VS.Vector (Complex Double)
  -> [(Int, Int, VS.Vector (Complex Double))]
unpackIrrepsFlat secs midsOf buf =
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
  let mat = denseFIrreps a b c
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
  cupCoeff _ tj =
    let fs = if even tj then 1 else -1
        dim = fromIntegral (tj + 1) :: Double
     in (fs * dim) :+ 0
