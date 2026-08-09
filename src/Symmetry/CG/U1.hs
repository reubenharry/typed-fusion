{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | U(1) fuse into coalesced charge layout matching @'Tensor' U1@.
--
-- Input is the Kronecker @toArray@ buffer of @C (RepDim r) ⊗ C (RepDim q)@
-- (second factor fastest). Output groups equal total charges, sorted by
-- @chargeInteger@ (same order as type-level @CmpZ@), with multiplicity copies
-- contiguous.
module Symmetry.CG.U1
  ( fuseU1Flat
  ) where

import Control.Monad.ST (runST)
import Data.Complex (Complex)
import Data.Proxy (Proxy (..))
import qualified Data.Map.Strict as Map
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Storable.Mutable as MVS
import GHC.TypeLits (natVal)
import Symmetry.ChargeEq (chargeInteger)
import Symmetry.Group (Group (U1))
import Symmetry.RepSingleton (SRep (..))

-- | @(charge, multiplicity, flat offset)@ for a U(1) spine.
sectorsU1 :: SRep U1 r -> [(Integer, Int, Int)]
sectorsU1 = go 0
  where
    go :: Int -> SRep U1 r0 -> [(Integer, Int, Int)]
    go _ SRepNilU1 = []
    go !off (SRepCons @z @m sz rest) =
      let ch = chargeInteger sz
          mult = fromIntegral (natVal (Proxy @m))
      in  (ch, mult, off) : go (off + mult) rest

repDimOf :: [(Integer, Int, Int)] -> Int
repDimOf [] = 0
repDimOf secs =
  let (_, m, off) = last secs
  in  off + m

-- | Pack product buffer into coalesced @'Tensor' U1@ layout.
fuseU1Flat
  :: SRep U1 r
  -> SRep U1 q
  -> VS.Vector (Complex Double)
  -> VS.Vector (Complex Double)
fuseU1Flat sr sq vin =
  let secsR = sectorsU1 sr
      secsQ = sectorsU1 sq
      dimQ = repDimOf secsQ
      contribs =
        [ (z1 + z2, m1 * m2, z1, m1, off1, z2, m2, off2)
        | (z1, m1, off1) <- secsR
        , (z2, m2, off2) <- secsQ
        ]
      multByZ =
        Map.fromListWith (+) [ (z, dm) | (z, dm, _, _, _, _, _, _) <- contribs ]
      sortedZs = Map.keys multByZ
      outOffByZ =
        Map.fromList $
          zip sortedZs (scanl (+) 0 [ multByZ Map.! z | z <- sortedZs ])
      dimF = case sortedZs of
        [] -> 0
        _ ->
          let z = last sortedZs
          in  (outOffByZ Map.! z) + (multByZ Map.! z)
      μ0ByZ = Map.fromList [ (z, 0) | z <- sortedZs ]
  in  runST $ do
        vout <- MVS.replicate dimF 0
        let writeContrib μCursors (zOut, dmult, _z1, m1, off1, _z2, m2, off2) = do
              let μBase = μCursors Map.! zOut
                  outOff0 = outOffByZ Map.! zOut
              mapM_
                ( \(μ1, μ2) -> do
                    let μLocal = μ1 * m2 + μ2
                        μOut = μBase + μLocal
                        iR = off1 + μ1
                        iQ = off2 + μ2
                    MVS.write vout (outOff0 + μOut) (vin VS.! (iR * dimQ + iQ))
                )
                [ (μ1, μ2) | μ1 <- [0 .. m1 - 1], μ2 <- [0 .. m2 - 1] ]
              pure (Map.insert zOut (μBase + dmult) μCursors)
        _ <- foldM writeContrib μ0ByZ contribs
        VS.freeze vout
  where
    foldM _ z [] = pure z
    foldM f z (x : xs) = do
      z' <- f z x
      foldM f z' xs
