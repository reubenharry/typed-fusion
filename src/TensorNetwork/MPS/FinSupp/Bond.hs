{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

module TensorNetwork.MPS.FinSupp.Bond where

import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import Data.List (foldl')
import Data.VectorSpace.Free.FiniteSupportedSequence (FinSuppSeq (..))
import Math.LinearMap.Category
  ( type (+>), type (⊗), LinearMap (..), Tensor (..), AdditiveGroup (..), getLinearMap
  , VectorSpace ((*^)), Scalar, sumV )
import GHC.TypeLits (KnownNat)
import Numeric.LinearAlgebra.Static (C, Sized (..))
import qualified Data.Vector.Storable as VS
import Data.Complex (Complex)
import TensorNetwork.MPS.General (BulkSite, MPS (..))
import Linear.V (V)
import GHC.TypeNats (natVal)
import Data.Data (Proxy(..))
import Data.Maybe (fromMaybe)
import qualified Numeric.LinearAlgebra as LA

type Field = Complex Double
type Bond = FinSuppSeq Field

bondCoeff :: Bond -> Int -> Field
bondCoeff (FinSuppSeq v) i = if i < U.length v then v U.! i else 0

bondLength :: Bond -> Int
bondLength (FinSuppSeq v) = U.length v

scaleBond :: Field -> Bond -> Bond
scaleBond μ (FinSuppSeq v) = FinSuppSeq (U.map (μ *) v)

addBondPadded :: Bond -> Bond -> Bond
addBondPadded (FinSuppSeq a) (FinSuppSeq b) =
  let n = max (U.length a) (U.length b)
  in FinSuppSeq $
       U.generate n $ \i ->
         (if i < U.length a then a U.! i else 0)
           + (if i < U.length b then b U.! i else 0)

-- | Embed a bond vector into @C n@ (zero-padded); @n@ must cover active support.
bondToC :: forall n. KnownNat n => Bond -> C n
bondToC (FinSuppSeq v) =
  fromMaybe (error "bondToC: dimension too small for bond support") $
    create (LA.fromList (padTo dim (U.toList v)))
  where
    dim = fromIntegral (natVal (Proxy @n))
    padTo k xs = xs ++ replicate (max 0 (k - length xs)) 0


applyBondMap :: (VectorSpace w, Scalar w ~ Field) => Bond -> Bond +> w -> w
applyBondMap b (LinearMap imgs) =
  let n = max (bondLength b) (length imgs)
  in sumV
       [ bondCoeff b i *^ imgAt i
       | i <- [0 .. n - 1]
       ]
  where
    imgAt i
      | i < length imgs = imgs !! i
      | otherwise       = zeroV

-- applyBulkSiteBond :: KnownNat p => V p (BulkSite Bond phys) -> Bond -> Int -> Bond
-- applyBulkSiteBond ( (LinearMap imgs)) bond s =
--   foldr addBondPadded (FinSuppSeq U.empty) $
--     [ scaleBond (bondCoeff bond i) (rows V.! s)
--     | (i, Tensor rows) <- zip [0 ..] imgs
--     ]

vpDim :: forall p. KnownNat p => Int
vpDim = fromIntegral (natVal (Proxy @p))

cvpCoeff :: KnownNat p => C p -> Int -> Field
cvpCoeff v s = (VS.toList (extract v)) !! s

-- | Apply a bulk site to a bond vector and full physical vector.
applyBulkBondPhys :: forall p phys. KnownNat p => V p (BulkSite Bond phys) -> Bond -> C p -> Bond
applyBulkBondPhys site bond phys =
  sumV
    [ cvpCoeff phys s *^ undefined site bond s
    | s <- [0 .. vpDim @p - 1]
    ]

activeDimBond :: Bond -> Int
activeDimBond (FinSuppSeq v)
  | U.null v  = 0
  | otherwise = 1 + go (U.length v - 1)
  where
    go i
      | i < 0        = 0
      | v U.! i /= 0 = i + 1
      | otherwise    = go (i - 1)

offsetBond :: Int -> Bond -> Bond
offsetBond 0 b = b
offsetBond n (FinSuppSeq v)
  | n <= 0    = FinSuppSeq v
  | otherwise = FinSuppSeq (U.replicate n 0 U.++ v)

type BondVec = V.Vector Bond

activeDimIntoBond :: BondVec -> Int
activeDimIntoBond = V.foldl' max 0 . V.map activeDimBond

offsetBondVec :: Int -> BondVec -> BondVec
offsetBondVec n = V.map (offsetBond n)

offsetCodomainIntoBond
  :: Int -> (C vp +> Bond) -> (C vp +> Bond)
offsetCodomainIntoBond n (LinearMap imgs) =
  LinearMap (offsetBondVec n imgs)

isZeroBond :: Bond -> Bool
isZeroBond (FinSuppSeq v) = U.all (== 0) v

activeDimCenterSite :: forall vp. KnownNat vp => [C vp ⊗ Bond] -> Int
activeDimCenterSite imgs =
  foldl'
    (\acc (i, Tensor rows) ->
       if V.any (not . isZeroBond) rows then i + 1 else acc)
    0
    (zip [0 ..] imgs)

activeDimCenterOut :: forall vp. KnownNat vp => [C vp ⊗ Bond] -> Int
activeDimCenterOut imgs =
  maximum $
    0 :
      [ activeDimBond row
      | Tensor rows <- imgs
      , row <- V.toList rows
      ]

activeDimRightSite :: forall vp. KnownNat vp => [C vp] -> Int
activeDimRightSite imgs =
  foldl' (\acc (i, v) -> if v == zeroV then acc else i + 1) 0 (zip [0 ..] imgs)

padLinearMapDomain :: AdditiveGroup w => Int -> [w] -> [w]
padLinearMapDomain chi imgs =
  take chi (imgs ++ replicate (max 0 (chi - length imgs)) zeroV)

padCenterDomain
  :: forall vp. KnownNat vp => Int -> Bond +> (C vp ⊗ Bond) -> Bond +> (C vp ⊗ Bond)
padCenterDomain chi (LinearMap imgs) =
  LinearMap (padLinearMapDomain chi imgs)

padRightDomain
  :: forall vp. KnownNat vp => Int -> Bond +> C vp -> Bond +> C vp
padRightDomain chi (LinearMap imgs) =
  LinearMap (padLinearMapDomain chi imgs)

bondDimMPS :: forall vp phys. KnownNat vp => MPS Bond phys vp -> Int
bondDimMPS (MPS ( l) ( c) ( r)) = undefined
    -- maximum
    --   [ activeDimIntoBond (getLinearMap l)
    --   -- , activeDimCenterSite (getLinearMap c)
    --   -- , activeDimCenterOut (getLinearMap c)
    --   -- , activeDimRightSite (getLinearMap r)
    --   ]

offsetBondInTensor
  :: Int -> (C vp ⊗ Bond) -> (C vp ⊗ Bond)
offsetBondInTensor n (Tensor tp) = Tensor (V.map (offsetBond n) tp)

addIntoBondMap
  :: KnownNat vp => Int -> (C vp +> Bond) -> (C vp +> Bond) -> (C vp +> Bond)
addIntoBondMap chiF f g = f ^+^ offsetCodomainIntoBond chiF g

fuseBondPair :: Int -> Int -> Bond -> Bond -> Bond
fuseBondPair chiA chiB (FinSuppSeq a) (FinSuppSeq b) =
  FinSuppSeq $
    U.generate (chiA * chiB) $ \k ->
      let i = k `mod` chiA
          j = k `div` chiA
          ai = if i < U.length a then a U.! i else 0
          bj = if j < U.length b then b U.! j else 0
      in ai * bj
