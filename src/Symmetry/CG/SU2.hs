{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

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
  , fuseSU2FlatSectors
  , unfuseSU2Flat
  , unfuseSU2FlatSectors
  , fuseMapRightFlat
  , fuseMapRightFlatSectors
  , fuseMapLeftFlatSectors
  , fuseTreeLeftSectors
  , fuseTreeRightSectors
  , fmoveFlatSectors
  , fusedSectorPairs
  , sectorsFromPairs
  , fuseCGChannel
  , unfuseCGChannel
  , cgMatrixTwoIrreps
  , cgChannel
  , fusionChannels
  , sectorsSU2
  , repDimOf
  ) where

import Control.Arrow.Constrained (arr)
import Control.Monad.ST (runST)
import Data.Complex (Complex (..))
import Data.Proxy (Proxy (..))
import Data.Singletons (fromSing)
import GHC.TypeLits (KnownNat, Nat, natVal, type (+))
import Data.VectorSpace (Scalar)
import Math.LinearMap.Category
  ( type (+>), type (⊗), LSpace, TensorSpace
  , LinearFunction, pattern LinearFunction
  )
import Control.Arrow.Constrained (arr)
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.LinearMap.Category.Instances ()
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import Numeric.LinearAlgebra.Static (C)
import qualified Data.Map.Strict as Map
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Storable.Mutable as MVS
import qualified Numeric.LinearAlgebra as LA
import Symmetry.Group (Group (SU2))
import Symmetry.RepSingleton (KnownRep (..), SRep (..), repSing)

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

-- | Product-basis bras @⟨j m_k|@ for a single total-@tj@ channel (Condon–Shortley).
-- Each inner list has length @(j1+1)*(j2+1)@, column order @k2@-fast — same as
-- 'cgMatrixTwoIrreps'.  Apply by pairing with a separable amplitude list
-- @[u_k1 * v_k2]@.
cgChannel :: Int -> Int -> Int -> [[Double]]
cgChannel j1 j2 tj =
  let mat = cgMatrixTwoIrreps j1 j2
      chans = fusionChannels j1 j2
      row0 = sum [c + 1 | c <- takeWhile (/= tj) chans]
  in  take (tj + 1) (drop row0 mat)

-- | One total-@j@ CG channel as a typed linear map on irrep legs
-- (@C (j₁+1) ⊗ C (j₂+1) → C (j+1)@). Densifies 'cgChannel' once per
-- monomorphic use, then applies via hmatrix @#>@.
fuseCGChannel
  :: forall j1 j2 j
   . ( KnownNat j1
     , KnownNat j2
     , KnownNat j
     , KnownNat (j1 + 1)
     , KnownNat (j2 + 1)
     , KnownNat (j + 1)
     , LSpace (C (j1 + 1))
     , LSpace (C (j2 + 1))
     , LSpace (C (j + 1))
     , LSpace (C (j1 + 1) ⊗ C (j2 + 1))
     , TensorSpace (C (j1 + 1) ⊗ C (j2 + 1))
     , Scalar (C (j1 + 1)) ~ Complex Double
     , Scalar (C (j2 + 1)) ~ Complex Double
     , Scalar (C (j + 1)) ~ Complex Double
     , Scalar (C (j1 + 1) ⊗ C (j2 + 1)) ~ Complex Double
     )
  => (C (j1 + 1) ⊗ C (j2 + 1)) +> C (j + 1)
fuseCGChannel = arr (LinearFunction applyCG)
  where
    tj1 = fromIntegral (natVal (Proxy @j1)) :: Int
    tj2 = fromIntegral (natVal (Proxy @j2)) :: Int
    tj = fromIntegral (natVal (Proxy @j)) :: Int
    dIn = (tj1 + 1) * (tj2 + 1)
    dOut = tj + 1
    -- Densify CG rows once per monomorphic channel; apply as mat-vec.
    !matFlat =
      VS.fromList
        [c :+ 0 | row <- cgChannel tj1 tj2 tj, c <- row]
    applyCG :: C (j1 + 1) ⊗ C (j2 + 1) -> C (j + 1)
    applyCG v =
      let vin = toArray v
       in unsafeFromArray @(C (j + 1)) $
            VS.generate dOut $ \row ->
              VS.sum $
                VS.zipWith
                  (*)
                  (VS.slice (row * dIn) dIn matFlat)
                  vin

-- | Inverse of 'fuseCGChannel' on the channel image (real CG ⇒ transpose).
unfuseCGChannel
  :: forall j1 j2 j
   . ( KnownNat j1
     , KnownNat j2
     , KnownNat j
     , KnownNat (j1 + 1)
     , KnownNat (j2 + 1)
     , KnownNat (j + 1)
     , LSpace (C (j1 + 1))
     , LSpace (C (j2 + 1))
     , LSpace (C (j + 1))
     , LSpace (C (j1 + 1) ⊗ C (j2 + 1))
     , TensorSpace (C (j1 + 1) ⊗ C (j2 + 1))
     , Scalar (C (j1 + 1)) ~ Complex Double
     , Scalar (C (j2 + 1)) ~ Complex Double
     , Scalar (C (j + 1)) ~ Complex Double
     , Scalar (C (j1 + 1) ⊗ C (j2 + 1)) ~ Complex Double
     )
  => C (j + 1) +> (C (j1 + 1) ⊗ C (j2 + 1))
unfuseCGChannel = arr (LinearFunction applyUnfuse)
  where
    tj1 = fromIntegral (natVal (Proxy @j1)) :: Int
    tj2 = fromIntegral (natVal (Proxy @j2)) :: Int
    tj = fromIntegral (natVal (Proxy @j)) :: Int
    dIn = (tj1 + 1) * (tj2 + 1)
    dOut = tj + 1
    !matFlat =
      VS.fromList
        [c :+ 0 | row <- cgChannel tj1 tj2 tj, c <- row]
    applyUnfuse :: C (j + 1) -> C (j1 + 1) ⊗ C (j2 + 1)
    applyUnfuse w =
      let win = toArray w
       in unsafeFromArray @(C (j1 + 1) ⊗ C (j2 + 1)) $
            VS.generate dIn $ \col ->
              VS.sum $
                VS.generate dOut $ \row ->
                  (matFlat VS.! (row * dIn + col)) * (win VS.! row)

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
fuseSU2Flat sr sq =
  fuseSU2FlatSectors (sectorsSU2 sr) (sectorsSU2 sq)

-- | Sector-list form of 'fuseSU2Flat' (@(tj, multiplicity, offset)@ spines).
fuseSU2FlatSectors
  :: [(Int, Int, Int)]
  -> [(Int, Int, Int)]
  -> VS.Vector (Complex Double)
  -> VS.Vector (Complex Double)
fuseSU2FlatSectors secsR secsQ vin =
  let dimQ = repDimOf secsQ
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

-- | @(tj, multiplicity)@ → offset spine for 'fuseSU2FlatSectors'.
sectorsFromPairs :: [(Int, Int)] -> [(Int, Int, Int)]
sectorsFromPairs = go 0
  where
    go _ [] = []
    go !off ((tj, m) : rest) =
      (tj, m, off) : go (off + m * (tj + 1)) rest

-- | Inverse of 'fuseSU2Flat' (real CG ⇒ transpose): fused multiplet layout →
-- Kronecker product @Forget(r) ⊗ Forget(q)@ (@iR * dimQ + iQ@). Same total
-- dimension — unitary isomorphism, not an embedding into a larger space.
unfuseSU2Flat
  :: SRep SU2 r
  -> SRep SU2 q
  -> VS.Vector (Complex Double)
  -> VS.Vector (Complex Double)
unfuseSU2Flat sr sq =
  unfuseSU2FlatSectors (sectorsSU2 sr) (sectorsSU2 sq)

unfuseSU2FlatSectors
  :: [(Int, Int, Int)]
  -> [(Int, Int, Int)]
  -> VS.Vector (Complex Double)
  -> VS.Vector (Complex Double)
unfuseSU2FlatSectors secsR secsQ vout =
  let dimIn = repDimOf secsR * repDimOf secsQ
      e i = VS.generate dimIn (\j -> if j == i then 1 else 0)
   in VS.generate dimIn $ \i ->
        VS.sum $ VS.zipWith (*) (fuseSU2FlatSectors secsR secsQ (e i)) vout

-- | Naturality of fuse on the right: @refuse ∘ (id ⊗ f) ∘ unfuse@.
-- @f@ acts on the forgetful flat of @q@ (@dimQ → dimQ'@).
fuseMapRightFlat
  :: SRep SU2 r
  -> SRep SU2 q
  -> SRep SU2 q'
  -> (VS.Vector (Complex Double) -> VS.Vector (Complex Double))
  -> VS.Vector (Complex Double)
  -> VS.Vector (Complex Double)
fuseMapRightFlat sr sq sq' =
  fuseMapRightFlatSectors (sectorsSU2 sr) (sectorsSU2 sq) (sectorsSU2 sq')

-- | Sector-list form of 'fuseMapRightFlat'.
fuseMapRightFlatSectors
  :: [(Int, Int, Int)]
  -> [(Int, Int, Int)]
  -> [(Int, Int, Int)]
  -> (VS.Vector (Complex Double) -> VS.Vector (Complex Double))
  -> VS.Vector (Complex Double)
  -> VS.Vector (Complex Double)
fuseMapRightFlatSectors secsR secsQ secsQ' f vin =
  let unfused = unfuseSU2FlatSectors secsR secsQ vin
      dimQ = repDimOf secsQ
      dimR = repDimOf secsR
      mapped =
        VS.concat
          [ f (VS.slice (iR * dimQ) dimQ unfused)
          | iR <- [0 .. dimR - 1]
          ]
   in fuseSU2FlatSectors secsR secsQ' mapped

-- | Naturality of fuse on the left: @refuse ∘ (f ⊗ id) ∘ unfuse@.
fuseMapLeftFlatSectors
  :: [(Int, Int, Int)]
  -> [(Int, Int, Int)]
  -> [(Int, Int, Int)]
  -> (VS.Vector (Complex Double) -> VS.Vector (Complex Double))
  -> VS.Vector (Complex Double)
  -> VS.Vector (Complex Double)
fuseMapLeftFlatSectors secsR secsR' secsQ f vin =
  let unfused = unfuseSU2FlatSectors secsR secsQ vin
      dimQ = repDimOf secsQ
      dimR = repDimOf secsR
      dimR' = repDimOf secsR'
      mapped = runST $ do
        m <- MVS.replicate (dimR' * dimQ) 0
        mapM_
          ( \iQ -> do
              let fiber =
                    VS.generate dimR $ \iR -> unfused VS.! (iR * dimQ + iQ)
                  fiber' = f fiber
              mapM_
                ( \iR' ->
                    MVS.write m (iR' * dimQ + iQ) (fiber' VS.! iR')
                )
                [0 .. dimR' - 1]
          )
          [0 .. dimQ - 1]
        VS.freeze m
   in fuseSU2FlatSectors secsR' secsQ mapped

-- | Output @(tj, multiplicity)@ pairs of CG-fusing two forgetful spines.
fusedSectorPairs :: [(Int, Int)] -> [(Int, Int)] -> [(Int, Int)]
fusedSectorPairs r q =
  Map.toAscList $
    Map.fromListWith
      (+)
      [ (tjOut, m1 * m2)
      | (tj1, m1) <- r
      , (tj2, m2) <- q
      , tjOut <- fusionChannels tj1 tj2
      ]

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

-- | Dense F (or @Fᵀ ≈ F⁻¹@) on left\/right coalesced flats of @r⊗q⊗s@.
-- Same densification as 'Symmetry.CG.FSymbol.denseFMove', sector-list driven.
fmoveFlatSectors
  :: Bool
  -> [(Int, Int, Int)]
  -> [(Int, Int, Int)]
  -> [(Int, Int, Int)]
  -> VS.Vector (Complex Double)
  -> VS.Vector (Complex Double)
fmoveFlatSectors inv secsR secsQ secsS vin =
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
      mat = mR LA.<> LA.tr mL
      v = VS.convert vin :: LA.Vector (Complex Double)
      v' =
        if inv
          then LA.tr mat LA.#> v
          else mat LA.#> v
   in VS.convert v'
  where
    pairsOf secs = [(tj, m) | (tj, m, _) <- secs]
