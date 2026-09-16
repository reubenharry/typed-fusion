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
-- Type-level labels are @Label SU2Th = Nat@ (@2j@). Term-level @TermLab = Int@.
-- Spin fractions have kind 'SpinKind' (@1/2@, @3/2@, …); reduce with 'Spin' to a
-- @2j@ label (@Spin (1/2) = 1@, @Spin (1/1) = 2@).
--
-- 'fSymbol' is closed-form Wigner 6j ('su2FAmpTJ'); production F-move apply
-- uses 'Fusion.ChannelF.fmoveChannelsD' on those scalars (no densify \/ mat-vec).
-- CG densify lives only in 'Hom.Reference' (@quantum-reference@ package).
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
  , fmoveIrrepsFlat
  , fmoveChannels
  , packIrrepsFlat
  , unpackIrrepsFlat
  , applySchurF
  ) where

import Data.Complex (Complex (..), magnitude)
import Data.Maybe (mapMaybe)
import Data.Proxy (Proxy (..))
import qualified Data.Map.Strict as Map
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Storable.Mutable as MVS
import Fusion.ChannelF (fmoveChannelsD)
import Fusion.Data (FusionData (..), allowedLeftMids, allowedRightMids)
import Fusion.Theory (FusionTheory (..), Label)
import GHC.TypeLits (Nat, type (*), type Div)
import Symmetry.CG.SixJ (su2FAmpTJ)
import Symmetry.CG.SU2
  ( fusedSectorPairs
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

type instance Label SU2Th = Nat

instance FusionTheory Nat SU2Th where
  type UnitLab SU2Th = 0
  type FuseN SU2Th j1 j2 = TensorIrrepRepSU2 j1 j2
  type DualLab SU2Th j = j

su2FuseOutcomes :: Int -> Int -> [(Int, Int)]
su2FuseOutcomes j1 j2 = [(j, 1) | j <- fusionChannels j1 j2]

-- | Channel R-phase for bosonic SU(2): @(-1)^{j₁+j₂-j}@ with labels as @2j@.
su2RPhase :: Int -> Int -> Int -> Complex Double
su2RPhase tj1 tj2 tj
  | odd (tj1 + tj2 - tj) =
      error "su2RPhase: tj1+tj2-tj must be even (invalid fusion channel)"
  | even ((tj1 + tj2 - tj) `div` 2) = 1
  | otherwise = -1

--------------------------------------------------------------------------------
-- Term-level F-symbols (irrep triples)
--------------------------------------------------------------------------------

canFuseTJ :: Int -> Int -> Int -> Bool
canFuseTJ = canFuseD (Proxy @SU2Th)

-- | Left intermediates @e@ for @((a⊗b)e)⊗c → d@.
allowedE :: Int -> Int -> Int -> Int -> [Int]
allowedE = allowedLeftMids (Proxy @SU2Th)

-- | Right intermediates @f@ for @a⊗((b⊗c)f) → d@.
allowedF :: Int -> Int -> Int -> Int -> [Int]
allowedF = allowedRightMids (Proxy @SU2Th)

-- | Sector layout of left-fused @((a⊗b)⊗c)@: @(tj, mult, flat offset)@.
leftSectors :: Int -> Int -> Int -> [(Int, Int, Int)]
leftSectors a b c =
  let ab = fusedSectorPairs [(a, 1)] [(b, 1)]
   in sectorsFromPairs (fusedSectorPairs ab [(c, 1)])

rightSectors :: Int -> Int -> Int -> [(Int, Int, Int)]
rightSectors a b c =
  let bc = fusedSectorPairs [(b, 1)] [(c, 1)]
   in sectorsFromPairs (fusedSectorPairs [(a, 1)] bc)

-- | Multiplicity-block entry @[F^{abc}_d]_{ef}@ (closed-form 6j).
fMultEntry
  :: Int -> Int -> Int -> Int -> Int -> Int -> Complex Double
fMultEntry = su2FAmpTJ

-- | Screenshot F-symbol: @|(ab)e;c;d⟩ = Σ_f [F^{abc}_d]_{ef} |a;(bc)f;d⟩@.
-- @inv@ yields @[F^{-1}]_{ef} = [F]_{fe}@ (real orthogonal F).
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
        ( \fLab ->
            let amp =
                  if inv
                    then su2FAmpTJ a b c d fLab e -- [F^{-1}]_{e f} = [F]_{f e}
                    else su2FAmpTJ a b c d e fLab
             in if magnitude amp < 1e-14
                  then Nothing
                  else Just (fLab, amp)
        )
        (allowedF a b c d)

--------------------------------------------------------------------------------
-- Schur apply (@F ⊗ I_{d+1}@) — LA-free
--------------------------------------------------------------------------------

-- | Apply multiplicity F as @{F ⊗ I_dim}@ (@inv@: @Fᵀ ⊗ I@).
-- @blk!!f!!e = [F]_{e f}@ with rows = right mids, cols = left mids.
applySchurF
  :: Bool
  -> [[Complex Double]]
  -> Int
  -> VS.Vector (Complex Double)
  -> VS.Vector (Complex Double)
applySchurF inv blk dim vin =
  let ne = case blk of
        (row : _) -> length row
        [] -> 0
      nf = length blk
      -- forward: out[f*dim+m] = sum_e blk[f][e] * in[e*dim+m]
      -- inv: out[e*dim+m] = sum_f blk[f][e] * in[f*dim+m]  (Fᵀ)
   in if inv
        then
          VS.generate (ne * dim) $ \i ->
            let e = i `div` dim
                m = i `mod` dim
             in sum
                  [ (blk !! f) !! e * (vin VS.! (f * dim + m))
                  | f <- [0 .. nf - 1]
                  ]
        else
          VS.generate (nf * dim) $ \i ->
            let f = i `div` dim
                m = i `mod` dim
             in sum
                  [ (blk !! f) !! e * (vin VS.! (e * dim + m))
                  | e <- [0 .. ne - 1]
                  ]

-- | Per-total channel F on irrep payloads (@C (d+1)@ each) via 'fSymbol'.
fmoveChannels
  :: Bool
  -> Int
  -> Int
  -> Int
  -> [(Int, Int, VS.Vector (Complex Double))]
  -> [(Int, Int, VS.Vector (Complex Double))]
fmoveChannels = fmoveChannelsD (Proxy @SU2Th) (\d -> d + 1)

-- | Left↔right F on irrep-triple flats via 'fmoveChannels' (pack \/ unpack).
fmoveIrrepsFlat
  :: Bool
  -> Int
  -> Int
  -> Int
  -> VS.Vector (Complex Double)
  -> VS.Vector (Complex Double)
fmoveIrrepsFlat inv a b c vin =
  let secsIn = if inv then rightSectors a b c else leftSectors a b c
      secsOut = if inv then leftSectors a b c else rightSectors a b c
      midsIn = if inv then allowedF a b c else allowedE a b c
      midsOut = if inv then allowedE a b c else allowedF a b c
      chIn = unpackIrrepsFlat secsIn midsIn vin
      chOut = fmoveChannels inv a b c chIn
   in packIrrepsFlat secsOut midsOut chOut

--------------------------------------------------------------------------------
-- Pack \/ unpack channel flats
--------------------------------------------------------------------------------

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
