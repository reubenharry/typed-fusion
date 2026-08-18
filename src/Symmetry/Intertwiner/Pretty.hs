{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Pretty-printing for Schur-block intertwiners.
--
-- Shows both the coefficient (Schur) blocks labeled by irrep and the expanded
-- dense matrix in sector-block form (@M_{m,n}(ℂ) ⊗ I_{dim j}@ for SU(2)).
module Symmetry.Intertwiner.Pretty
  ( PrettyInter (..)
  , ppr
  , pprDense
  ) where

import Data.Complex (Complex (..))
import Data.List (intercalate)
import Data.Proxy (Proxy (..))
import Data.Singletons (fromSing)
import GHC.TypeLits (KnownNat, natVal)
import qualified Numeric.LinearAlgebra as LA
import Numeric.LinearAlgebra.Static (unwrap)
import Text.Printf (printf)
import Symmetry.FunctorExperiment
  ( IntertwinerG (..), IntertwinerSectorsG (..)
  , RepLookup (..), targetIrrepOffset
  , LookupResult (..)
  )
import Symmetry.Group
  ( Group (..), Rep, RepDimG, SectorDim, IrrepDim )
import Symmetry.HomBlock
  ( coeffBlockAsMat, su2ExpandBlock )
import Symmetry.RepSingleton (SRep (..), KnownRep (..))
import Symmetry.Utils (Z (..))

-- | REPL helpers.
ppr :: PrettyInter g r q => IntertwinerG g r q -> IO ()
ppr = putStrLn . prettyIntertwiner

pprDense :: PrettyInter g r q => IntertwinerG g r q -> IO ()
pprDense = putStrLn . prettyIntertwinerDense

class PrettyInter (g :: Group) (r :: Rep g) (q :: Rep g) where
  -- | Schur blocks + sector layout.
  prettyIntertwiner :: IntertwinerG g r q -> String
  -- | Expanded dense forgetful matrix (block-diagonal).
  prettyIntertwinerDense :: IntertwinerG g r q -> String

instance
  ( KnownRep U1 r, KnownRep U1 q
  , KnownNat (RepDimG U1 r), KnownNat (RepDimG U1 q)
  , RepLookup U1
  ) => PrettyInter U1 r q where
  prettyIntertwiner (MkIntertwiner hom) =
    prettyGoU1 (repSing @U1 @r) (repSing @U1 @q) hom
      (fromIntegral (natVal (Proxy @(RepDimG U1 r))))
      (fromIntegral (natVal (Proxy @(RepDimG U1 q))))
  prettyIntertwinerDense (MkIntertwiner hom) =
    renderDenseMatrix
      (fromIntegral (natVal (Proxy @(RepDimG U1 q))))
      (fromIntegral (natVal (Proxy @(RepDimG U1 r))))
      (denseBlocksU1 (repSing @U1 @r) (repSing @U1 @q) hom 0)

instance
  ( KnownRep SU2 r, KnownRep SU2 q
  , KnownNat (RepDimG SU2 r), KnownNat (RepDimG SU2 q)
  , RepLookup SU2
  ) => PrettyInter SU2 r q where
  prettyIntertwiner (MkIntertwiner hom) =
    prettyGoSU2 (repSing @SU2 @r) (repSing @SU2 @q) hom
      (fromIntegral (natVal (Proxy @(RepDimG SU2 r))))
      (fromIntegral (natVal (Proxy @(RepDimG SU2 q))))
  prettyIntertwinerDense (MkIntertwiner hom) =
    renderDenseMatrix
      (fromIntegral (natVal (Proxy @(RepDimG SU2 q))))
      (fromIntegral (natVal (Proxy @(RepDimG SU2 r))))
      (denseBlocksSU2 (repSing @SU2 @r) (repSing @SU2 @q) hom 0)

--------------------------------------------------------------------------------
-- Labels / formatting
--------------------------------------------------------------------------------

prettyZU1 :: Z -> String
prettyZU1 Zero = "0"
prettyZU1 (Pos n) = '+' : show n
prettyZU1 (Neg n) = '-' : show n

prettySU2 :: Integral a => a -> String
prettySU2 tj
  | even tj' = show (tj' `div` 2)
  | otherwise = show tj' ++ "/2"
  where
    tj' = toInteger tj

prettyC :: Complex Double -> String
prettyC (a :+ b)
  | abs b < 1e-12 && abs a < 1e-12 = "0"
  | abs b < 1e-12 = printf "%.2g" a
  | abs a < 1e-12 = printf "%.2gj" b
  | b >= 0 = printf "%.2g+%.2gj" a b
  | otherwise = printf "%.2g%.2gj" a b

prettyMat :: LA.Matrix (Complex Double) -> String
prettyMat mat =
  let cells = map (map prettyC) (LA.toLists mat)
      widths = foldr (zipWith max . map length) (repeat 0) cells
      padL w s = replicate (w - length s) ' ' ++ s
      fmt row = intercalate "  " (zipWith padL widths row)
  in  intercalate "\n" (map (("    " ++) . fmt) cells)

--------------------------------------------------------------------------------
-- Schur-block views
--------------------------------------------------------------------------------

prettyGoU1
  :: SRep U1 r -> SRep U1 q -> IntertwinerSectorsG U1 hom
  -> Int -> Int -> String
prettyGoU1 sr sq hom dimR dimQ =
  unlines $
    [ "Intertwiner U(1)  dim " ++ show dimR ++ " → " ++ show dimQ
    , "Schur blocks (charge → multiplicity matrix):"
    ]
      ++ emptyOrNone (schurBlocksU1 sr sq hom 0)
      ++ [""]
      ++ sectorLinesU1 "domain" sr
      ++ sectorLinesU1 "codomain" sq

emptyOrNone :: [String] -> [String]
emptyOrNone [] = ["  (none)"]
emptyOrNone xs = xs

schurBlocksU1
  :: SRep U1 r -> SRep U1 q -> IntertwinerSectorsG U1 hom -> Int -> [String]
schurBlocksU1 SRepNilU1 _ _ _ = []
schurBlocksU1 (SRepCons @z @m saz rest) sq InterNil off =
  let stride :: Int
      stride = fromIntegral (natVal (Proxy @(SectorDim U1 z m)))
  in  case sLookupMult @U1 saz sq of
        Absent -> schurBlocksU1 rest sq InterNil (off + stride)
        Present{} -> ["  <hom spine exhausted>"]
schurBlocksU1 (SRepCons @z @m saz rest) sq (InterCons blk homRest) off =
  let stride :: Int
      stride = fromIntegral (natVal (Proxy @(SectorDim U1 z m)))
  in  case sLookupMult @U1 saz sq of
        Absent -> schurBlocksU1 rest sq (InterCons blk homRest) (off + stride)
        Present (_ :: Proxy n) ->
          let mat = unwrap (coeffBlockAsMat blk)
              hdr =
                printf "  charge %s  mult %d→%d  @col %d:"
                  (prettyZU1 (fromSing saz))
                  (fromIntegral (natVal (Proxy @m)) :: Int)
                  (fromIntegral (natVal (Proxy @n)) :: Int)
                  off
          in  (hdr : lines (prettyMat mat))
                ++ schurBlocksU1 rest sq homRest (off + stride)

sectorLinesU1 :: String -> SRep U1 r -> [String]
sectorLinesU1 tag SRepNilU1 = ["  " ++ tag ++ " sectors: (empty)"]
sectorLinesU1 tag s = ("  " ++ tag ++ " sectors:") : goSec s 0
  where
    goSec :: SRep U1 r' -> Int -> [String]
    goSec SRepNilU1 _ = []
    goSec (SRepCons @z @m saz rest) !off =
      let stride :: Int
          stride = fromIntegral (natVal (Proxy @(SectorDim U1 z m)))
          line =
            printf "    charge %s ×%d  [%d..%d)"
              (prettyZU1 (fromSing saz))
              (fromIntegral (natVal (Proxy @m)) :: Int)
              off (off + stride)
      in  line : goSec rest (off + stride)

prettyGoSU2
  :: SRep SU2 r -> SRep SU2 q -> IntertwinerSectorsG SU2 hom
  -> Int -> Int -> String
prettyGoSU2 sr sq hom dimR dimQ =
  unlines $
    [ "Intertwiner SU(2)  dim " ++ show dimR ++ " → " ++ show dimQ
    , "Schur blocks (j → multiplicity matrix; expands as ⊗ I_{2j+1}):"
    ]
      ++ emptyOrNone (schurBlocksSU2 sr sq hom 0)
      ++ [""]
      ++ sectorLinesSU2 "domain" sr
      ++ sectorLinesSU2 "codomain" sq

schurBlocksSU2
  :: SRep SU2 r -> SRep SU2 q -> IntertwinerSectorsG SU2 hom -> Int -> [String]
schurBlocksSU2 SRepNilSU2 _ _ _ = []
schurBlocksSU2 (SRepConsSU2 @j @m saj rest) sq InterNil off =
  let stride :: Int
      stride = fromIntegral (natVal (Proxy @(SectorDim SU2 j m)))
  in  case sLookupMult @SU2 saj sq of
        SU2Absent -> schurBlocksSU2 rest sq InterNil (off + stride)
        SU2Present{} -> ["  <hom spine exhausted>"]
schurBlocksSU2 (SRepConsSU2 @j @m saj rest) sq (InterCons blk homRest) off =
  let stride :: Int
      stride = fromIntegral (natVal (Proxy @(SectorDim SU2 j m)))
      irrepD :: Int
      irrepD = fromIntegral (natVal (Proxy @(IrrepDim SU2 j)))
  in  case sLookupMult @SU2 saj sq of
        SU2Absent -> schurBlocksSU2 rest sq (InterCons blk homRest) (off + stride)
        SU2Present (_ :: Proxy n) ->
          let mat = unwrap (coeffBlockAsMat blk)
              mI = fromIntegral (natVal (Proxy @m)) :: Int
              nI = fromIntegral (natVal (Proxy @n)) :: Int
              hdr =
                printf "  j=%s  mult %d→%d  expands %d×%d  @col %d:"
                  (prettySU2 (fromSing saj)) mI nI (mI * irrepD) (nI * irrepD) off
          in  (hdr : lines (prettyMat mat))
                ++ schurBlocksSU2 rest sq homRest (off + stride)

sectorLinesSU2 :: String -> SRep SU2 r -> [String]
sectorLinesSU2 tag SRepNilSU2 = ["  " ++ tag ++ " sectors: (empty)"]
sectorLinesSU2 tag s = ("  " ++ tag ++ " sectors:") : goSec s 0
  where
    goSec :: SRep SU2 r' -> Int -> [String]
    goSec SRepNilSU2 _ = []
    goSec (SRepConsSU2 @j @m saj rest) !off =
      let stride :: Int
          stride = fromIntegral (natVal (Proxy @(SectorDim SU2 j m)))
          line =
            printf "    j=%s ×%d  [%d..%d)"
              (prettySU2 (fromSing saj))
              (fromIntegral (natVal (Proxy @m)) :: Int)
              off (off + stride)
      in  line : goSec rest (off + stride)

--------------------------------------------------------------------------------
-- Dense expanded matrix
--------------------------------------------------------------------------------

type BlockStamp = (Int, Int, LA.Matrix (Complex Double))

denseBlocksU1
  :: KnownRep U1 q
  => SRep U1 r -> SRep U1 q -> IntertwinerSectorsG U1 hom -> Int -> [BlockStamp]
denseBlocksU1 SRepNilU1 _ _ _ = []
denseBlocksU1 (SRepCons @z @m saz rest) sq InterNil off =
  let stride :: Int
      stride = fromIntegral (natVal (Proxy @(SectorDim U1 z m)))
  in  case sLookupMult @U1 saz sq of
        Absent -> denseBlocksU1 rest sq InterNil (off + stride)
        Present{} -> []
denseBlocksU1 (SRepCons @z @m saz rest) sq (InterCons blk homRest) off =
  let stride :: Int
      stride = fromIntegral (natVal (Proxy @(SectorDim U1 z m)))
  in  case sLookupMult @U1 saz sq of
        Absent -> denseBlocksU1 rest sq (InterCons blk homRest) (off + stride)
        Present (_ :: Proxy n) ->
          (targetIrrepOffset @U1 saz sq, off, unwrap (coeffBlockAsMat blk))
            : denseBlocksU1 rest sq homRest (off + stride)

denseBlocksSU2
  :: KnownRep SU2 q
  => SRep SU2 r -> SRep SU2 q -> IntertwinerSectorsG SU2 hom -> Int -> [BlockStamp]
denseBlocksSU2 SRepNilSU2 _ _ _ = []
denseBlocksSU2 (SRepConsSU2 @j @m saj rest) sq InterNil off =
  let stride :: Int
      stride = fromIntegral (natVal (Proxy @(SectorDim SU2 j m)))
  in  case sLookupMult @SU2 saj sq of
        SU2Absent -> denseBlocksSU2 rest sq InterNil (off + stride)
        SU2Present{} -> []
denseBlocksSU2 (SRepConsSU2 @j @m saj rest) sq (InterCons blk homRest) off =
  let stride :: Int
      stride = fromIntegral (natVal (Proxy @(SectorDim SU2 j m)))
  in  case sLookupMult @SU2 saj sq of
        SU2Absent -> denseBlocksSU2 rest sq (InterCons blk homRest) (off + stride)
        SU2Present (_ :: Proxy n) ->
          (targetIrrepOffset @SU2 saj sq, off, unwrap (su2ExpandBlock @j blk))
            : denseBlocksSU2 rest sq homRest (off + stride)

renderDenseMatrix :: Int -> Int -> [BlockStamp] -> String
renderDenseMatrix rows cols stamps =
  let zero = LA.konst 0 (rows, cols) :: LA.Matrix (Complex Double)
      stamped =
        foldl
          ( \acc (r0, c0, blk) ->
              let (br, bc) = LA.size blk
                  rowsAcc = LA.toLists acc
                  rowsBlk = LA.toLists blk
              in  LA.fromLists
                    [ if ri >= r0 && ri < r0 + br
                        then
                          let brow = rowsBlk !! (ri - r0)
                          in  [ if ci >= c0 && ci < c0 + bc
                                  then brow !! (ci - c0)
                                  else rowsAcc !! ri !! ci
                              | ci <- [0 .. cols - 1]
                              ]
                        else rowsAcc !! ri
                    | ri <- [0 .. rows - 1]
                    ]
          )
          zero
          stamps
  in  unlines
        [ "Dense forgetful matrix (" ++ show rows ++ "×" ++ show cols ++ "), block-diagonal:"
        , prettyMat stamped
        ]
