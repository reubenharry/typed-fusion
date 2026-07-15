{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeFamilies #-}

module TensorNetwork.MPS.FinSupp.VectorSpace where

-- import Math.LinearMap.Category
--   ( LinearMap (..), AdditiveGroup (..), VectorSpace (..), getLinearMap, (*^) )
-- import GHC.TypeLits (KnownNat)
-- import Numeric.LinearAlgebra.Static (C)
-- import TensorNetwork.MPS.FinSupp.Bond
--   ( bondDimMPS, addIntoBondMap, padCenterDomain, padRightDomain
--   , offsetBondInTensor )

-- zeroMPS :: KnownNat p => MPS p
-- zeroMPS = MPS (LeftSite zeroV) (BulkSite zeroV) (RightSite zeroV)

-- addMPS :: KnownNat p => MPS p -> MPS p -> MPS p
-- addMPS m1 m2 =
--   let chi1 = bondDimMPS m1
--       chi2 = bondDimMPS m2
--       MPS (LeftSite l1) (BulkSite c1) (RightSite r1) = m1
--       MPS (LeftSite l2) (BulkSite c2) (RightSite r2) = m2
--       c1' = padCenterDomain chi1 c1
--       c2' = padCenterDomain chi2 c2
--       r1' = padRightDomain chi1 r1
--       r2' = padRightDomain chi2 r2
--   in MPS
--        (LeftSite (addIntoBondMap chi1 l1 l2))
--        (BulkSite (LinearMap $ getLinearMap c1' ++ map (offsetBondInTensor chi1) (getLinearMap c2')))
--        (RightSite (LinearMap $ getLinearMap r1' ++ getLinearMap r2'))

-- scaleMPS :: KnownNat p => Field -> MPS p -> MPS p
-- scaleMPS μ (MPS (LeftSite l) (BulkSite c) (RightSite r)) =
--   MPS (LeftSite (μ *^ l)) (BulkSite (μ *^ c)) (RightSite (μ *^ r))

-- instance KnownNat p => AdditiveGroup (MPS p) where
--   zeroV = zeroMPS
--   (^+^) = addMPS
--   negateV m = scaleMPS (-1) m

-- instance KnownNat p => VectorSpace (MPS p) where
--   type Scalar (MPS p) = Field
--   μ *^ m = scaleMPS μ m
