{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Generic skeletal tensor \/ braid \/ associator from 'FusionData'.
--
-- Each Hom sector is emitted as Dual-left @C n_s(X) +> C n_s(Y)@ (no matrix
-- densify buffer, no pack\/unpack).
module Fusion.Ops
  ( tensorHomDual
  , braidHomDual
  , associateHomDual
  , disassociateHomDual
  , channelPairs
  , multOf
  , idxXY
  , vacuumPairing
  ) where

import Control.Arrow.Constrained (arr, ($))
import Control.Monad (guard)
import Data.Complex (Complex)
import Data.List (elemIndex, findIndex, foldl')
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import Data.Vector.Storable (toList)
import Data.VectorSpace (AdditiveGroup (zeroV))
import Fusion.Data (FusionData (..))
import Fusion.Hom
  ( HomDualS (..)
  , SectorDual
  , fillHomDual
  , sectorFromMap
  , sectorToMap
  )
import Fusion.Theory (FiniteIrr (..), Label)
import GHC.TypeLits (KnownNat, natVal)
import Math.LinearMap.Category
  ( DualVector
  , pattern LinearFunction
  , type (⊗)
  )
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.LinearMap.Category.Instances ()
import Math.OrphanInstances ()
import Numeric.LinearAlgebra.Static (C, Sized (fromList, unwrap))
import Numeric.LinearAlgebra.Static.COrphans ()
import Prelude hiding (($))

--------------------------------------------------------------------------------
-- Dual-left sector spine builders
--------------------------------------------------------------------------------

-- | Existential Dual-left sector (lookup by Irr index).
data SomeSector where
  SomeSector
    :: SectorDual nd nc
    => DualVector (C nd) ⊗ C nc
    -> SomeSector

homSectors :: HomDualS nsDom nsCod -> [SomeSector]
homSectors HomDualNil = []
homSectors (HomDualCons t rest) = SomeSector t : homSectors rest

sectorLin
  :: forall nd nc
   . SectorDual nd nc
  => (C nd -> C nc)
  -> DualVector (C nd) ⊗ C nc
sectorLin f = sectorFromMap (arr (LinearFunction f))

coords :: forall n. KnownNat n => C n -> [Complex Double]
coords = toList . unwrap

fromCoords :: forall n. KnownNat n => [Complex Double] -> C n
fromCoords = fromList

applySectorCoords :: SomeSector -> [Complex Double] -> [Complex Double]
applySectorCoords (SomeSector (t :: DualVector (C nd) ⊗ C nc)) vin =
  coords @nc (sectorToMap t $ fromCoords @nd vin)

zeroSector
  :: forall nd nc
   . SectorDual nd nc
  => DualVector (C nd) ⊗ C nc
zeroSector = zeroV

--------------------------------------------------------------------------------
-- N-basis channels
--------------------------------------------------------------------------------

multOf :: (Eq lab) => [lab] -> [Int] -> lab -> Int
multOf irr ms s =
  case elemIndex s irr of
    Just i | i < length ms -> ms !! i
    _ -> 0

channelPairs
  :: forall t
   . (FiniteIrr (Label t) t, FusionData (Label t) t, Eq (Label t), TermLab t ~ Label t)
  => Proxy t
  -> Label t
  -> [(Label t, Label t)]
channelPairs p c =
  let irr = irrVals p
   in [ (x, y)
      | x <- irr
      , y <- irr
      , canFuseD p x y c
      ]

channelOffset
  :: forall t
   . (FiniteIrr (Label t) t, FusionData (Label t) t, Eq (Label t), TermLab t ~ Label t)
  => Proxy t
  -> [Int]
  -> [Int]
  -> Label t
  -> Label t
  -> Label t
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

idxXY
  :: forall t
   . (FiniteIrr (Label t) t, FusionData (Label t) t, Eq (Label t), TermLab t ~ Label t)
  => Proxy t
  -> [Int]
  -> [Int]
  -> Label t
  -> Int
  -> Label t
  -> Int
  -> Label t
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

sectorChargeSize
  :: forall t
   . (FiniteIrr (Label t) t, FusionData (Label t) t, Eq (Label t), TermLab t ~ Label t)
  => Proxy t
  -> [Int]
  -> [Int]
  -> Label t
  -> Int
sectorChargeSize p nx ny c =
  let irr = irrVals p
   in sum [multOf irr nx x * multOf irr ny y | (x, y) <- channelPairs p c]

sectorMult
  :: forall t
   . (FiniteIrr (Label t) t, FusionData (Label t) t, Eq (Label t), TermLab t ~ Label t)
  => Proxy t
  -> [Int]
  -> [Int]
  -> [Int]
sectorMult p nx ny =
  map (sectorChargeSize p nx ny) (irrVals p)

--------------------------------------------------------------------------------
-- Sparse / block actions on coordinate lists (define Dual-left maps)
--------------------------------------------------------------------------------

addAt :: Int -> Complex Double -> [Complex Double] -> [Complex Double]
addAt i v xs =
  [ if k == i then xs !! k + v else xs !! k
  | k <- [0 .. length xs - 1]
  ]

-- | Kronecker of two sector maps on flat N-basis blocks.
kronCoords
  :: ([Complex Double] -> [Complex Double])
  -> Int
  -> Int
  -> ([Complex Double] -> [Complex Double])
  -> Int
  -> Int
  -> [Complex Double]
  -> [Complex Double]
kronCoords f r1 c1 g r2 c2 vin =
  let vout0 = replicate (r1 * r2) 0
      -- column-major blocks: input index = i1 * c2 + i2  with i1 in cols of f, i2 in cols of g
      -- row-major flatten of kron: out (i1,i2) at i1*r2+i2 for rows; in (j1,j2) at j1*c2+j2
   in foldl'
        ( \acc j ->
            let j1 = j `div` c2
                j2 = j `mod` c2
                -- unit vector e_j maps under kron to kron(f e_j1, g e_j2)
                ej1 = [if k == j1 then 1 else 0 | k <- [0 .. c1 - 1]]
                ej2 = [if k == j2 then 1 else 0 | k <- [0 .. c2 - 1]]
                fj = f ej1
                gj = g ej2
                col =
                  [ fj !! i1 * gj !! i2
                  | i1 <- [0 .. r1 - 1]
                  , i2 <- [0 .. r2 - 1]
                  ]
             in foldl'
                  (\a (i, x) -> addAt i ((vin !! j) * x) a)
                  acc
                  (zip [0 ..] col)
        )
        vout0
        [0 .. c1 * c2 - 1]

blockDiagApply
  :: [([Complex Double] -> [Complex Double], Int, Int)]
  -> [Complex Double]
  -> [Complex Double]
blockDiagApply blocks vin =
  let domOff = scanl (+) 0 [c | (_, _, c) <- blocks]
      codOff = scanl (+) 0 [r | (_, r, _) <- blocks]
      nOut = last codOff
   in foldl'
        ( \acc ((f, r, c), di, ci) ->
            let blockIn = take c (drop di vin)
                blockOut = f blockIn
             in foldl'
                  (\a (k, x) -> addAt (ci + k) x a)
                  acc
                  (zip [0 .. r - 1] blockOut)
        )
        (replicate nOut 0)
        (zip3 blocks (init domOff) (init codOff))

commuteApply :: Int -> Int -> Complex Double -> [Complex Double] -> [Complex Double]
commuteApply n m phase vin
  | n == 0 || m == 0 = replicate (m * n) 0
  | otherwise =
      let vout0 = replicate (m * n) 0
       in foldl'
            ( \acc i ->
                foldl'
                  ( \a j ->
                      let src = i * m + j
                          dst = j * n + i
                       in addAt dst (phase * (vin !! src)) a
                  )
                  acc
                  [0 .. m - 1]
            )
            vout0
            [0 .. n - 1]

--------------------------------------------------------------------------------
-- Tensor \/ braid \/ associator (Dual-left)
--------------------------------------------------------------------------------

kronBlock
  :: SomeSector
  -> SomeSector
  -> ([Complex Double] -> [Complex Double], Int, Int)
kronBlock sf@(SomeSector (_ :: DualVector (C n1) ⊗ C m1)) sg@(SomeSector (_ :: DualVector (C n2) ⊗ C m2)) =
  let n1i = fromIntegral (natVal (Proxy @n1)) :: Int
      m1i = fromIntegral (natVal (Proxy @m1)) :: Int
      n2i = fromIntegral (natVal (Proxy @n2)) :: Int
      m2i = fromIntegral (natVal (Proxy @m2)) :: Int
   in ( kronCoords (applySectorCoords sf) m1i n1i (applySectorCoords sg) m2i n2i
      , m1i * m2i
      , n1i * n2i
      )

tensorHomDual
  :: forall t nsA nsB nsC nsD nsAC nsBD
   . ( FiniteIrr (Label t) t
     , FusionData (Label t) t
     , Eq (Label t)
     , TermLab t ~ Label t
     )
  => Proxy t
  -> HomDualS nsAC nsAC
  -> HomDualS nsBD nsBD
  -> HomDualS nsA nsB
  -> HomDualS nsC nsD
  -> HomDualS nsAC nsBD
tensorHomDual p idAC idBD f g =
  let irr = irrVals p
      fs = homSectors f
      gs = homSectors g
      at secs s =
        case elemIndex s irr of
          Just i | i < length secs -> secs !! i
          _ -> error "tensorHomDual: missing sector"
   in fillHomDual idAC idBD (\i (Proxy :: Proxy nd) (Proxy :: Proxy nc) ->
        let c = irr !! i
            pairs = channelPairs p c
         in if null pairs
              then zeroSector @nd @nc
              else
                let blocks = [kronBlock (at fs x) (at gs y) | (x, y) <- pairs]
                 in sectorLin @nd @nc (fromCoords @nc . blockDiagApply blocks . coords @nd)
      )

braidHomDual
  :: forall t nsAB nsBA
   . ( FiniteIrr (Label t) t
     , FusionData (Label t) t
     , Eq (Label t)
     , TermLab t ~ Label t
     )
  => Proxy t
  -> HomDualS nsAB nsAB
  -> HomDualS nsBA nsBA
  -> [Int]
  -> [Int]
  -> HomDualS nsAB nsBA
braidHomDual p idAB idBA na nb =
  let irr = irrVals p
   in fillHomDual idAB idBA (\i (Proxy :: Proxy nd) (Proxy :: Proxy nc) ->
        let c = irr !! i
            pairs = channelPairs p c
            domSizes = [multOf irr na x * multOf irr nb y | (x, y) <- pairs]
            codSizes = [multOf irr nb l * multOf irr na r | (l, r) <- pairs]
            domOff = scanl (+) 0 domSizes
            codOff = scanl (+) 0 codSizes
         in sectorLin @nd @nc $ \v ->
              let vin = coords @nd v
                  vout0 = replicate (fromIntegral (natVal (Proxy @nc))) 0
                  paint acc (x, y) =
                    case ( findIndex (\(u, w) -> u == x && w == y) pairs
                         , findIndex (\(u, w) -> u == y && w == x) pairs
                         ) of
                      (Just di, Just ci) ->
                        let col0 = domOff !! di
                            row0 = codOff !! ci
                            nx = multOf irr na x
                            ny = multOf irr nb y
                            phase = rSymbol p x y c
                            blkIn = take (nx * ny) (drop col0 vin)
                            blkOut = commuteApply nx ny phase blkIn
                         in foldl'
                              (\a (k, x') -> addAt (row0 + k) x' a)
                              acc
                              (zip [0 ..] blkOut)
                      _ -> acc
               in fromCoords @nc (foldl' paint vout0 pairs)
      )

leftCol'
  :: forall t
   . (FiniteIrr (Label t) t, FusionData (Label t) t, Eq (Label t), TermLab t ~ Label t)
  => Proxy t
  -> [Int]
  -> [Int]
  -> [Int]
  -> Label t
  -> Int
  -> Label t
  -> Int
  -> Label t
  -> Int
  -> Label t
  -> Label t
  -> Maybe Int
leftCol' p na nb nc a aI b bI c cI e total = do
  guard (canFuseD p a b e)
  guard (canFuseD p e c total)
  eIdx <- idxXY p na nb a aI b bI e
  let nab = sectorMult p na nb
  idxXY p nab nc e eIdx c cI total

rightRow'
  :: forall t
   . (FiniteIrr (Label t) t, FusionData (Label t) t, Eq (Label t), TermLab t ~ Label t)
  => Proxy t
  -> [Int]
  -> [Int]
  -> [Int]
  -> Label t
  -> Int
  -> Label t
  -> Int
  -> Label t
  -> Int
  -> Label t
  -> Label t
  -> Maybe Int
rightRow' p na nb nc a aI b bI c cI f total = do
  guard (canFuseD p b c f)
  guard (canFuseD p a f total)
  fIdx <- idxXY p nb nc b bI c cI f
  let nbc = sectorMult p nb nc
  idxXY p na nbc a aI f fIdx total

assocEntries
  :: forall t
   . (FiniteIrr (Label t) t, FusionData (Label t) t, Eq (Label t), TermLab t ~ Label t)
  => Proxy t
  -> Bool
  -> Label t
  -> [Int]
  -> [Int]
  -> [Int]
  -> [((Int, Int), Complex Double)]
assocEntries p inv total na nb nc =
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

applyEntries
  :: Int
  -> Int
  -> [((Int, Int), Complex Double)]
  -> [Complex Double]
  -> [Complex Double]
applyEntries nRows _nCols ents vin =
  foldl'
    ( \acc ((i, j), a) ->
        addAt i (a * (vin !! j)) acc
    )
    (replicate nRows 0)
    ents

associateHomDual
  :: forall t nsL nsR
   . ( FiniteIrr (Label t) t
     , FusionData (Label t) t
     , Eq (Label t)
     , TermLab t ~ Label t
     )
  => Proxy t
  -> HomDualS nsL nsL
  -> HomDualS nsR nsR
  -> [Int]
  -> [Int]
  -> [Int]
  -> HomDualS nsL nsR
associateHomDual p idL idR na nb nc =
  let irr = irrVals p
   in fillHomDual idL idR (\i (Proxy :: Proxy nd) (Proxy :: Proxy nc) ->
        let total = irr !! i
            nRows = fromIntegral (natVal (Proxy @nc))
            nCols = fromIntegral (natVal (Proxy @nd))
            ents = assocEntries p False total na nb nc
         in sectorLin @nd @nc $
              fromCoords @nc . applyEntries nRows nCols ents . coords @nd
      )

disassociateHomDual
  :: forall t nsL nsR
   . ( FiniteIrr (Label t) t
     , FusionData (Label t) t
     , Eq (Label t)
     , TermLab t ~ Label t
     )
  => Proxy t
  -> HomDualS nsL nsL
  -> HomDualS nsR nsR
  -> [Int]
  -> [Int]
  -> [Int]
  -> HomDualS nsL nsR
disassociateHomDual p idL idR na nb nc =
  let irr = irrVals p
   in fillHomDual idL idR (\i (Proxy :: Proxy nd) (Proxy :: Proxy nc) ->
        let total = irr !! i
            nRows = fromIntegral (natVal (Proxy @nc))
            nCols = fromIntegral (natVal (Proxy @nd))
            ents =
              [ ((col, row), amp)
              | ((row, col), amp) <- assocEntries p True total na nb nc
              ]
         in sectorLin @nd @nc $
              fromCoords @nc . applyEntries nRows nCols ents . coords @nd
      )

--------------------------------------------------------------------------------
-- Cups (coefficient source for Dual-left Fib cups)
--------------------------------------------------------------------------------

vacuumPairing
  :: forall t
   . (FiniteIrr (Label t) t, FusionData (Label t) t, Eq (Label t), TermLab t ~ Label t)
  => Proxy t
  -> [Int]
  -> [Int]
  -> (Label t -> Complex Double)
  -> [Complex Double]
vacuumPairing p nx ny weight =
  let irr = irrVals p
      u = unitVal p
      nVac = sectorChargeSize p nx ny u
      pairs =
        [ (i, weight j)
        | j <- irr
        , let nL = multOf irr nx j
              nR = multOf irr ny j
        , nL == nR
        , k <- [0 .. nL - 1]
        , Just i <- [idxXY p nx ny j k j k u]
        ]
   in foldl'
        (\ws (i, c) ->
           [ if k == i then ws !! k + c else ws !! k
           | k <- [0 .. nVac - 1]
           ]
        )
        (replicate nVac 0)
        pairs
