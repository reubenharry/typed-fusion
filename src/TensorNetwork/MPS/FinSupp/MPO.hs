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
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ConstraintKinds #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | FinSupp MPO apply / compose: exact @Bond ⊗ Bond@ product (via
-- 'TensorNetwork.MPS.General'), then Kronecker-fuse back to growable 'Bond'.
--
-- The growable bond closes under composition, giving a direct
-- @Category (MPO Bond n)@ instance.
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
  ) where

import Prelude hiding (id, ($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained (Category (..), id, (.))
import Control.Arrow.Constrained (($), arr)
import Data.Complex (Complex)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import qualified Data.Vector as Vector
import qualified Data.Vector.Unboxed as U
import qualified Numeric.LinearAlgebra as LA
import GHC.TypeLits (KnownNat, Nat, natVal)
import Linear.V (V (..))
import Math.LinearMap.Category
  ( type (+>), type (⊗), Tensor (..)
  , pattern LinearFunction
  , (-+$>)
  , tensorProduct, AdditiveGroup (zeroV)
  )
import Math.LinearMap.Category.Instances ()
import Numeric.LinearAlgebra.Static (C, Sized (create))
import Numeric.LinearAlgebra.Static.COrphans ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Data.VectorSpace.Free.FiniteSupportedSequence (FinSuppSeq (..))
import Control.Lens (view)
import TensorNetwork.Categorical ((⊗^))
import TensorNetwork.MPS.General
  ( MPS (..), MPO (..), MPSConstraints
  , mpoApplyExact, mpoComposeExact
  , mpoBondDimHint
  )
import TensorNetwork.MPS.FinSupp.Bond
  ( Bond, bondCoeff, activeDimBond )
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
  :: forall phys (n :: Nat).
  ( MPSConstraints Bond phys
  , MPSConstraints (Bond ⊗ Bond) phys
  ) =>
  Int -> Int ->
  MPS (Bond ⊗ Bond) phys n -> MPS Bond phys n
fuseMPSBondFS chiA chiB (MPS l bulk r) =
  let f = fuseBondLin chiA chiB
      s = splitBondLin chiA chiB
  in MPS
       (f . l)
       ((\site -> f . site . (s ⊗^ Cat.id)) <$> bulk)
       (r . s)

fuseMPOBondFS
  :: forall physIn physOut (n :: Nat).
  ( MPSConstraints Bond physIn
  , MPSConstraints Bond physOut
  , MPSConstraints (Bond ⊗ Bond) physIn
  , MPSConstraints (Bond ⊗ Bond) physOut
  ) =>
  Int -> Int ->
  MPO (Bond ⊗ Bond) n physIn physOut -> MPO Bond n physIn physOut
fuseMPOBondFS chiA chiB (MPO l bulk r _) =
  let f = fuseBondLin chiA chiB
      s = splitBondLin chiA chiB
  in MPO
       ((f ⊗^ Cat.id) . l)
       ((\site -> (f ⊗^ Cat.id) . site . (s ⊗^ Cat.id)) <$> bulk)
       (r . (s ⊗^ Cat.id))
       (chiA * chiB)

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

-- | Active virtual bond width of an MPS (from left-site support).
bondDimMPS :: forall p (n :: Nat). KnownNat p => MPS Bond (C p) n -> Int
bondDimMPS (MPS l _ _) =
  max 1 $
    maximum (0 : fmap activeDimBond (fmap (l $) (physBasis @p)))

-- | Runtime virtual-bond width carried explicitly by an MPO.
bondDimMPO :: MPO Bond n physIn physOut -> Int
bondDimMPO = max 1 . view mpoBondDimHint

--------------------------------------------------------------------------------
-- Identity, apply, compose
--------------------------------------------------------------------------------

unitBond :: Bond
unitBond = FinSuppSeq (U.singleton 1)

-- | Contract the unit bond factor: @(e₀ ⊗ p) ↦ p@.
identityRight
  :: forall phys. MPSConstraints Bond phys => (Bond ⊗ phys) +> phys
identityRight = arr $ LinearFunction $ \(Tensor rows) ->
  case rows of
    (p : _) -> p
    []      -> zeroV

-- | Bond-dimension-1 identity MPO on any category object.
identityMPO
  :: forall phys (q :: Nat).
  ( KnownNat q
  , MPSConstraints Bond phys
  ) =>
  MPO Bond q phys phys
identityMPO =
  MPO
    (arr (tensorProduct -+$> unitBond))
    (V . Vector.replicate qDim $ Cat.id)
    identityRight
    1
  where
    qDim = fromIntegral (natVal (Proxy @q))

-- | Apply an MPO to an MPS, fusing the product bond back to 'Bond'.
mpoApply
  :: forall p r (q :: Nat).
  ( KnownNat p
  , MPSConstraints Bond (C p)
  , MPSConstraints Bond (C r)
  , MPSConstraints (Bond ⊗ Bond) (C p)
  , MPSConstraints (Bond ⊗ Bond) (C r)
  ) =>
  MPO Bond q (C p) (C r) -> MPS Bond (C p) q -> MPS Bond (C r) q
mpoApply op psi =
  fuseMPSBondFS (bondDimMPO op) (bondDimMPS psi) (mpoApplyExact op psi)

-- | Operator product @h₁ ∘ h₂@ (apply @h₂@ then @h₁@), fused back to 'Bond'.
composeMPO
  :: forall a b c (q :: Nat).
  ( MPSConstraints Bond a
  , MPSConstraints Bond b
  , MPSConstraints Bond c
  , MPSConstraints (Bond ⊗ Bond) a
  , MPSConstraints (Bond ⊗ Bond) b
  , MPSConstraints (Bond ⊗ Bond) c
  ) =>
  MPO Bond q b c -> MPO Bond q a b -> MPO Bond q a c
composeMPO h1 h2 =
  fuseMPOBondFS (bondDimMPO h1) (bondDimMPO h2) (mpoComposeExact h1 h2)

--------------------------------------------------------------------------------
-- Category of FinSupp MPOs
--------------------------------------------------------------------------------

instance
  KnownNat q =>
  Category (MPO Bond q)
  where
  type Object (MPO Bond q) a =
    ( MPSConstraints Bond a
    , MPSConstraints (Bond ⊗ Bond) a
    )
  id = identityMPO
  (.) = composeMPO
