{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}

-- | FinSupp MPO apply / compose: exact @Bond ⊗ Bond@ product (via
-- 'TensorNetwork.MPS.General'), then Kronecker-fuse back to growable 'Bond'.
--
-- Also the tensor-network category @'TN'@ whose morphisms are MPOs and whose
-- @'Function'@ instance is MPO–MPS application.
module TensorNetwork.MPS.FinSupp.MPO
  ( Bond
  , fuseBondLin
  , splitBondLin
  , fuseMPSBondFS
  , fuseMPOBondFS
  , bondDimMPS
  , bondDimMPO
  , identityMPO
  , mpoApply
  , composeMPO
  , TN (..)
  ) where

import Prelude hiding (id, ($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained (Category (..), id, (.))
import Control.Arrow.Constrained (EnhancedCat (..), ($), arr)
import Data.Complex (Complex)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import Data.Foldable (toList)
import qualified Data.Vector as Vector
import qualified Data.Vector.Unboxed as U
import qualified Numeric.LinearAlgebra as LA
import GHC.TypeLits (KnownNat, Nat, natVal)
import Linear.V (V (..))
import Math.LinearMap.Category
  ( type (+>), type (⊗), Tensor (..), LinearMap (..)
  , pattern LinearFunction
  , TensorSpace (..), (-+$>)
  , tensorProduct, AdditiveGroup (zeroV)
  )
import Math.LinearMap.Category.Instances ()
import Numeric.LinearAlgebra.Static (C, Sized (create))
import Numeric.LinearAlgebra.Static.COrphans ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Data.VectorSpace.Free.FiniteSupportedSequence (FinSuppSeq (..))
import TensorNetwork.Categorical ((⊗^))
import TensorNetwork.MPS.General
  ( MPS (..), MPO (..), MPSConstraints
  , mpoApplyExact, mpoComposeExact
  )
import TensorNetwork.MPS.FinSupp.Bond
  ( Bond, Field, bondCoeff, activeDimBond )
import TensorNetwork.MPS.FinSupp.InnerSpace ()

--------------------------------------------------------------------------------
-- Kronecker fuse / split on growable bonds
--------------------------------------------------------------------------------

-- | Row-major Kronecker embed @Bond ⊗ Bond → Bond@ (@k = i + χₐ·j@).
fuseBondTensor :: Int -> Int -> Bond ⊗ Bond -> Bond
fuseBondTensor chiA chiB (Tensor cols) =
  let chiA' = max 1 chiA
      chiB' = max 1 chiB
      pad =
        take chiA' (cols ++ replicate (max 0 (chiA' - length cols)) zeroV)
  in FinSuppSeq $
       U.generate (chiA' * chiB') $ \k ->
         let i = k `mod` chiA'
             j = k `div` chiA'
         in bondCoeff (pad !! i) j

-- | Inverse of 'fuseBondTensor'.
splitBondTensor :: Int -> Int -> Bond -> Bond ⊗ Bond
splitBondTensor chiA chiB b =
  let chiA' = max 1 chiA
      chiB' = max 1 chiB
  in Tensor
       [ FinSuppSeq $ U.generate chiB' $ \j -> bondCoeff b (i + chiA' * j)
       | i <- [0 .. chiA' - 1]
       ]

fuseBondLin :: Int -> Int -> (Bond ⊗ Bond) +> Bond
fuseBondLin chiA chiB = arr (LinearFunction (fuseBondTensor chiA chiB))

splitBondLin :: Int -> Int -> Bond +> (Bond ⊗ Bond)
splitBondLin chiA chiB = arr (LinearFunction (splitBondTensor chiA chiB))

fuseMPSBondFS
  :: forall p (n :: Nat).
  ( KnownNat p
  , MPSConstraints Bond (C p)
  , MPSConstraints (Bond ⊗ Bond) (C p)
  ) =>
  Int -> Int ->
  MPS (Bond ⊗ Bond) (C p) n -> MPS Bond (C p) n
fuseMPSBondFS chiA chiB (MPS l bulk r) =
  let f = fuseBondLin chiA chiB
      s = splitBondLin chiA chiB
  in MPS
       (f . l)
       ((\site -> f . site . (s ⊗^ Cat.id)) <$> bulk)
       (r . s)

fuseMPOBondFS
  :: forall p (n :: Nat).
  ( KnownNat p
  , MPSConstraints Bond (C p)
  , MPSConstraints (Bond ⊗ Bond) (C p)
  ) =>
  Int -> Int ->
  MPO (Bond ⊗ Bond) (C p) n -> MPO Bond (C p) n
fuseMPOBondFS chiA chiB (MPO l bulk r) =
  let f = fuseBondLin chiA chiB
      s = splitBondLin chiA chiB
  in MPO
       ((f ⊗^ Cat.id) . l)
       ((\site -> (f ⊗^ Cat.id) . site . (s ⊗^ Cat.id)) <$> bulk)
       (r . (s ⊗^ Cat.id))

--------------------------------------------------------------------------------
-- Active bond widths (left-site support; meta only)
--------------------------------------------------------------------------------

vpDim :: forall p. KnownNat p => Int
vpDim = fromIntegral (natVal (Proxy @p))

physBasis :: forall p. KnownNat p => [C p]
physBasis =
  [ fromMaybe (error "physBasis") $
      create (LA.assoc (vpDim @p) 0 [(i, 1 :: Complex Double)])
  | i <- [0 .. vpDim @p - 1]
  ]

tensorBondWidth :: Bond ⊗ w -> Int
tensorBondWidth (Tensor rows) = length rows

-- | Active virtual bond width of an MPS (from left-site support).
bondDimMPS :: forall p (n :: Nat). KnownNat p => MPS Bond (C p) n -> Int
bondDimMPS (MPS l _ _) =
  max 1 $
    maximum (0 : fmap activeDimBond (fmap (l $) (physBasis @p)))

-- | Active virtual bond width of an MPO (from left-site support).
bondDimMPO :: forall p (n :: Nat). KnownNat p => MPO Bond (C p) n -> Int
bondDimMPO (MPO l _ _) =
  max 1 $
    maximum (0 : fmap (tensorBondWidth . (l $)) (physBasis @p))

--------------------------------------------------------------------------------
-- Identity, apply, compose
--------------------------------------------------------------------------------

unitBond :: Bond
unitBond = FinSuppSeq (U.singleton 1)

-- | Contract the unit bond factor: @(e₀ ⊗ p) ↦ p@.
identityRight
  :: forall p. (KnownNat p, AdditiveGroup (C p)) => (Bond ⊗ C p) +> C p
identityRight = arr $ LinearFunction $ \(Tensor rows) ->
  case rows of
    (p : _) -> p
    []      -> zeroV

-- | Bond-dimension-1 identity MPO on physical @C p@.
identityMPO
  :: forall p (q :: Nat).
  ( KnownNat p, KnownNat q
  , MPSConstraints Bond (C p)
  ) =>
  MPO Bond (C p) q
identityMPO =
  MPO
    (arr (tensorProduct -+$> unitBond))
    (V . Vector.replicate qDim $ Cat.id)
    identityRight
  where
    qDim = fromIntegral (natVal (Proxy @q))

-- | Apply an MPO to an MPS, fusing the product bond back to 'Bond'.
mpoApply
  :: forall p (q :: Nat).
  ( KnownNat p
  , MPSConstraints Bond (C p)
  , MPSConstraints (Bond ⊗ Bond) (C p)
  ) =>
  MPO Bond (C p) q -> MPS Bond (C p) q -> MPS Bond (C p) q
mpoApply op psi =
  fuseMPSBondFS (bondDimMPO op) (bondDimMPS psi) (mpoApplyExact op psi)

-- | Operator product @h₁ ∘ h₂@ (apply @h₂@ then @h₁@), fused back to 'Bond'.
composeMPO
  :: forall p (q :: Nat).
  ( KnownNat p
  , MPSConstraints Bond (C p)
  , MPSConstraints (Bond ⊗ Bond) (C p)
  ) =>
  MPO Bond (C p) q -> MPO Bond (C p) q -> MPO Bond (C p) q
composeMPO h1 h2 =
  fuseMPOBondFS (bondDimMPO h1) (bondDimMPO h2) (mpoComposeExact h1 h2)

--------------------------------------------------------------------------------
-- Category of MPOs acting on FinSupp MPS
--------------------------------------------------------------------------------

-- | Morphisms are MPOs; the (only) object is @MPS Bond (C p) q@.
data TN (p :: Nat) (q :: Nat) a b where
  TN :: MPO Bond (C p) q -> TN p q (MPS Bond (C p) q) (MPS Bond (C p) q)

instance
  ( KnownNat p, KnownNat q
  , MPSConstraints Bond (C p)
  , MPSConstraints (Bond ⊗ Bond) (C p)
  ) =>
  Category (TN p q)
  where
  type Object (TN p q) a = (a ~ MPS Bond (C p) q)
  id = TN identityMPO
  TN h1 . TN h2 = TN (composeMPO h1 h2)

-- | @'Function'@ instance: @h $ ψ = mpoApply h ψ@.
instance
  ( KnownNat p, KnownNat q
  , MPSConstraints Bond (C p)
  , MPSConstraints (Bond ⊗ Bond) (C p)
  ) =>
  EnhancedCat (->) (TN p q)
  where
  arr (TN h) = mpoApply h
