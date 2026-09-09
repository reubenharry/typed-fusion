{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Generic skeletal tensor \/ braid \/ associator from 'FusionData'.
module Fusion.Ops
  ( PackHom (..)
  , tensorSectors
  , braidSectors
  , associateSectors
  , disassociateSectors
  , channelPairs
  , multOf
  , idxXY
  , commuteKron
  , kronLA
  , blockDiagLA
  ) where

import Control.Monad (guard)
import Data.Complex (Complex)
import Data.List (elemIndex, findIndex)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import Fusion.Data (FusionData (..))
import Fusion.Theory (FiniteIrr (..))
import Fusion.Hom (HomS (..))
import GHC.TypeLits (KnownNat, Nat)
import qualified Numeric.LinearAlgebra as LA
import Numeric.LinearAlgebra.Static (Sized (create, unwrap))
import Prelude

--------------------------------------------------------------------------------
-- Pack \/ unpack HomS ↔ sector list
--------------------------------------------------------------------------------

class PackHom (nsDom :: [Nat]) (nsCod :: [Nat]) where
  unpackHom :: HomS nsDom nsCod -> [LA.Matrix (Complex Double)]
  packHom :: [LA.Matrix (Complex Double)] -> HomS nsDom nsCod

instance PackHom '[] '[] where
  unpackHom HomNil = []
  packHom [] = HomNil
  packHom _ = error "packHom: length mismatch (nil)"

instance (KnownNat nd, KnownNat nc, PackHom nds ncs) =>
  PackHom (nd ': nds) (nc ': ncs) where
  unpackHom (HomCons m rest) = unwrap m : unpackHom rest
  packHom (m : ms) =
    case create m of
      Just sm -> HomCons sm (packHom @nds @ncs ms)
      Nothing -> error "packHom: dimension mismatch"
  packHom [] = error "packHom: length mismatch (cons)"

--------------------------------------------------------------------------------
-- Linear-algebra helpers
--------------------------------------------------------------------------------

kronLA
  :: LA.Matrix (Complex Double)
  -> LA.Matrix (Complex Double)
  -> LA.Matrix (Complex Double)
kronLA = LA.kronecker

blockDiagLA :: [LA.Matrix (Complex Double)] -> LA.Matrix (Complex Double)
blockDiagLA [] = LA.konst 0 (0, 0)
blockDiagLA [m] = m
blockDiagLA (m : ms) =
  let rest = blockDiagLA ms
      (r1, c1) = LA.size m
      (r2, c2) = LA.size rest
   in LA.fromBlocks
        [ [m, LA.konst 0 (r1, c2)]
        , [LA.konst 0 (r2, c1), rest]
        ]

commuteKron :: Int -> Int -> Complex Double -> LA.Matrix (Complex Double)
commuteKron n m phase
  | n == 0 || m == 0 = LA.konst 0 (m * n, n * m)
  | otherwise =
      LA.accum (LA.konst 0 (m * n, n * m)) const $
        [ ((j * n + i, i * m + j), phase)
        | i <- [0 .. n - 1]
        , j <- [0 .. m - 1]
        ]

--------------------------------------------------------------------------------
-- N-basis channels
--------------------------------------------------------------------------------

multOf :: (Eq lab) => [lab] -> [Int] -> lab -> Int
multOf irr ms s =
  case elemIndex s irr of
    Just i | i < length ms -> ms !! i
    _ -> 0

-- | Pairs @(x,y)@ with @N_{xy}^c > 0@, in Irr×Irr order.
channelPairs
  :: forall lab t
   . (FiniteIrr lab t, FusionData lab t, Eq lab, TermLab t ~ lab)
  => Proxy t
  -> lab
  -> [(lab, lab)]
channelPairs p c =
  let irr = irrVals p
   in [ (x, y)
      | x <- irr
      , y <- irr
      , canFuseD p x y c
      ]

channelOffset
  :: forall lab t
   . (FiniteIrr lab t, FusionData lab t, Eq lab, TermLab t ~ lab)
  => Proxy t
  -> [Int]
  -> [Int]
  -> lab
  -> lab
  -> lab
  -> Int
channelOffset p nx ny c x y =
  let irr = irrVals p
      pairs = channelPairs p c
      idx =
        fromMaybe (error "channelOffset: missing pair") $
          findIndex (\(x', y') -> x' == x && y' == y) pairs
   in sum
        [ multOf irr nx x' * multOf irr ny y'
        | (x', y') <- take idx pairs
        ]

-- | Index of @x_i ⊗ y_j → c@ in the N-basis for @X ⊗ Y@.
idxXY
  :: forall lab t
   . (FiniteIrr lab t, FusionData lab t, Eq lab, TermLab t ~ lab)
  => Proxy t
  -> [Int]
  -> [Int]
  -> lab
  -> Int
  -> lab
  -> Int
  -> lab
  -> Maybe Int
idxXY p nx ny x ix y iy c = do
  guard (canFuseD p x y c)
  let irr = irrVals p
      mx = multOf irr nx x
      my = multOf irr ny y
  guard (ix >= 0 && ix < mx && iy >= 0 && iy < my)
  let off = channelOffset p nx ny c x y
  pure (off + ix * my + iy)

copies :: Int -> [Int]
copies n = [0 .. n - 1]

--------------------------------------------------------------------------------
-- Tensor
--------------------------------------------------------------------------------

tensorSectors
  :: forall lab t
   . (FiniteIrr lab t, FusionData lab t, Eq lab, TermLab t ~ lab)
  => Proxy t
  -> [Int]
  -> [Int]
  -> [Int]
  -> [Int]
  -> [LA.Matrix (Complex Double)]
  -> [LA.Matrix (Complex Double)]
  -> [LA.Matrix (Complex Double)]
tensorSectors p _nx _nz _ny _nw fs gs =
  let irr = irrVals p
      at mats s =
        case elemIndex s irr of
          Just i -> mats !! i
          Nothing -> LA.konst 0 (0, 0)
      forCharge c =
        let blocks =
              [ kronLA (at fs x) (at gs y)
              | (x, y) <- channelPairs p c
              ]
         in if null blocks then LA.konst 0 (0, 0) else blockDiagLA blocks
   in map forCharge irr

--------------------------------------------------------------------------------
-- Braid
--------------------------------------------------------------------------------

braidSectors
  :: forall lab t
   . (FiniteIrr lab t, FusionData lab t, Eq lab, TermLab t ~ lab)
  => Proxy t
  -> [Int]
  -> [Int]
  -> [LA.Matrix (Complex Double)]
braidSectors p na nb =
  let irr = irrVals p
      forCharge c =
        let pairs = channelPairs p c
            domSizes = [multOf irr na x * multOf irr nb y | (x, y) <- pairs]
            codSizes = [multOf irr nb l * multOf irr na r | (l, r) <- pairs]
            domOff = scanl (+) 0 domSizes
            codOff = scanl (+) 0 codSizes
            nCols = last domOff
            nRows = last codOff
            paint (x, y) =
              let Just di = findIndex (\(u, v) -> u == x && v == y) pairs
                  Just ci = findIndex (\(u, v) -> u == y && v == x) pairs
                  col0 = domOff !! di
                  row0 = codOff !! ci
                  nx = multOf irr na x
                  ny = multOf irr nb y
                  blk = commuteKron nx ny (rSymbol p x y c)
               in (row0, col0, blk)
         in if nRows == 0 || nCols == 0
              then LA.konst 0 (nRows, nCols)
              else
                foldl
                  ( \acc xy ->
                      let (row0, col0, blk) = paint xy
                          (br, bc) = LA.size blk
                          emb =
                            LA.accum (LA.konst 0 (nRows, nCols)) const $
                              [ ((row0 + i, col0 + j), blk `LA.atIndex` (i, j))
                              | i <- [0 .. br - 1]
                              , j <- [0 .. bc - 1]
                              ]
                       in acc + emb
                  )
                  (LA.konst 0 (nRows, nCols) :: LA.Matrix (Complex Double))
                  pairs
   in map forCharge irr

--------------------------------------------------------------------------------
-- Associator
--------------------------------------------------------------------------------

sectorChargeSize
  :: forall lab t
   . (FiniteIrr lab t, FusionData lab t, Eq lab, TermLab t ~ lab)
  => Proxy t
  -> [Int]
  -> [Int]
  -> lab
  -> Int
sectorChargeSize p nx ny c =
  let irr = irrVals p
   in sum [multOf irr nx x * multOf irr ny y | (x, y) <- channelPairs p c]

sectorMult
  :: forall lab t
   . (FiniteIrr lab t, FusionData lab t, Eq lab, TermLab t ~ lab)
  => Proxy t
  -> [Int]
  -> [Int]
  -> [Int]
sectorMult p nx ny =
  map (sectorChargeSize p nx ny) (irrVals p)

-- Simpler leftCol using ab mults:
leftCol'
  :: forall lab t
   . (FiniteIrr lab t, FusionData lab t, Eq lab, TermLab t ~ lab)
  => Proxy t
  -> [Int]
  -> [Int]
  -> [Int]
  -> lab
  -> Int
  -> lab
  -> Int
  -> lab
  -> Int
  -> lab
  -> lab
  -> Maybe Int
leftCol' p na nb nc a aI b bI c cI e total = do
  guard (canFuseD p a b e)
  guard (canFuseD p e c total)
  eIdx <- idxXY p na nb a aI b bI e
  let nab = sectorMult p na nb
  idxXY p nab nc e eIdx c cI total

rightRow'
  :: forall lab t
   . (FiniteIrr lab t, FusionData lab t, Eq lab, TermLab t ~ lab)
  => Proxy t
  -> [Int]
  -> [Int]
  -> [Int]
  -> lab
  -> Int
  -> lab
  -> Int
  -> lab
  -> Int
  -> lab -- ^ intermediate f
  -> lab -- ^ total
  -> Maybe Int
rightRow' p na nb nc a aI b bI c cI f total = do
  guard (canFuseD p b c f)
  guard (canFuseD p a f total)
  fIdx <- idxXY p nb nc b bI c cI f
  let nbc = sectorMult p nb nc
  idxXY p na nbc a aI f fIdx total

assocSectorEntries
  :: forall lab t
   . (FiniteIrr lab t, FusionData lab t, Eq lab, TermLab t ~ lab)
  => Proxy t
  -> Bool
  -> lab -- ^ total charge
  -> [Int]
  -> [Int]
  -> [Int]
  -> [((Int, Int), Complex Double)]
assocSectorEntries p inv total na nb nc =
  let irr = irrVals p
   in [ ((row, col), amp)
      | a <- irr
      , aI <- copies (multOf irr na a)
      , b <- irr
      , bI <- copies (multOf irr nb b)
      , c <- irr
      , cI <- copies (multOf irr nc c)
      , e <- irr
      , canFuseD p a b e
      , canFuseD p e c total
      , Just col <- [leftCol' p na nb nc a aI b bI c cI e total]
      , (f, amp) <- fSymbol p inv a b c total e
      , Just row <- [rightRow' p na nb nc a aI b bI c cI f total]
      ]

buildAssoc
  :: forall lab t
   . (FiniteIrr lab t, FusionData lab t, Eq lab, TermLab t ~ lab)
  => Proxy t
  -> Bool
  -> [Int]
  -> [Int]
  -> [Int]
  -> [LA.Matrix (Complex Double)]
buildAssoc p inv na nb nc =
  let irr = irrVals p
      nab = sectorMult p na nb
      nbc = sectorMult p nb nc
      nL s = sectorChargeSize p nab nc s -- ((a⊗b)⊗c)
      nR s = sectorChargeSize p na nbc s -- (a⊗(b⊗c))
      forCharge total =
        let nRows = if inv then nL total else nR total
            nCols = if inv then nR total else nL total
            ents = assocSectorEntries p inv total na nb nc
            -- For inverse, swap row/col interpretation: entries still (row,col) from
            -- leftCol/rightRow with inv F — matching Fibonacci disassociate by
            -- swapping left/right helpers at call site.
         in if nRows == 0 || nCols == 0
              then LA.konst 0 (nRows, nCols)
              else LA.accum (LA.konst 0 (nRows, nCols)) (+) ents
   in map forCharge irr

associateSectors
  :: forall lab t
   . (FiniteIrr lab t, FusionData lab t, Eq lab, TermLab t ~ lab)
  => Proxy t
  -> [Int]
  -> [Int]
  -> [Int]
  -> [LA.Matrix (Complex Double)]
associateSectors p na nb nc = buildAssoc p False na nb nc

disassociateSectors
  :: forall lab t
   . (FiniteIrr lab t, FusionData lab t, Eq lab, TermLab t ~ lab)
  => Proxy t
  -> [Int]
  -> [Int]
  -> [Int]
  -> [LA.Matrix (Complex Double)]
disassociateSectors p na nb nc =
  -- Inverse: domain is right-associated; rebuild with inv F and swapped indexers
  let irr = irrVals p
      nab = sectorMult p na nb
      nbc = sectorMult p nb nc
      nL s = sectorChargeSize p nab nc s
      nR s = sectorChargeSize p na nbc s
      forCharge total =
        let nRows = nL total
            nCols = nR total
            ents =
              [ ((col, row), amp) -- transpose of forward indexing with F^{-1}
              | a <- irr
              , aI <- copies (multOf irr na a)
              , b <- irr
              , bI <- copies (multOf irr nb b)
              , c <- irr
              , cI <- copies (multOf irr nc c)
              , e <- irr
              , canFuseD p a b e
              , canFuseD p e c total
              , Just col <- [leftCol' p na nb nc a aI b bI c cI e total]
              , (f, amp) <- fSymbol p True a b c total e
              , Just row <- [rightRow' p na nb nc a aI b bI c cI f total]
              ]
         in if nRows == 0 || nCols == 0
              then LA.konst 0 (nRows, nCols)
              else LA.accum (LA.konst 0 (nRows, nCols)) (+) ents
   in map forCharge irr
