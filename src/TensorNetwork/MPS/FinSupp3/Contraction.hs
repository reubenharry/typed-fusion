{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE NoStarIsType #-}

-- | Categorical MPS contraction (mirrors 'TensorNetwork.MPS.Fixed3').
--
-- Site maps are converted to transfer orientation on 'Bond', composed with
-- '⊗^' / unitors / associators, then closed to 'Physical3' via
-- 'transposeMap' — no basis-sum decode.
module TensorNetwork.MPS.FinSupp3.Contraction
  ( leftTransfer
  , bulkTransfer
  , rightTransfer
  , mpsChainMap
  , mpsChainClose
  , permuteFlatLegs13
  ) where

import Prelude hiding (id, ($), (.))
import Data.List (foldl')
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (arr, ($))
import Math.LinearMap.Category
  ( type (+>), type (⊗), (⊗), (-+$>), LinearFunction, pattern LinearFunction )
import Math.LinearMap.Coercion (uncurryLinearMap, (-+$=>))
import Data.VectorSpace (VectorSpace ((*^)), InnerSpace ((<.>)))
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Backend.HMatrix ()
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C)
import GHC.TypeLits (KnownNat, type (*))
import Math.VectorSpace.DimensionAware (toArray)
import qualified Data.Vector.Storable as VS
import TensorNetwork.Categorical
  ( (⊗^), rassocMap, lunit )
import TensorNetwork.Dagger (transposeMap)
import TensorNetwork.MPS.FinSupp3.Bond (applyBulkBondPhys)
import TensorNetwork.MPS.FinSupp3.Internal
  ( Bond, Field, LeftSite (..), BulkSite (..), RightSite (..), MPS (..), Physical3
  , withMPS3, one1, vpDim, basisCvp )

idC :: forall n. KnownNat n => C n +> C n
idC = Cat.id

-- | Co-lex flat index @(s₁,s₂,s₃) ↦ s₁ + p·s₂ + p²·s₃@ (matches 'mpsToFlat').
flatIndex3 :: Int -> Int -> Int -> Int -> Int
flatIndex3 p s1 s2 s3 = s1 + p * s2 + p * p * s3

-- | Swap @s₁ ↔ s₃@ in the co-lex flat array for @C p ⊗ (C p ⊗ C p)@.
--
-- Uncurried bulk/right transfers plus 'transposeMap' close the chain with the
-- first and third physical legs exchanged; this permutation restores the
-- canonical 'flatIndex3' / 'toArray' order.
permuteFlatLegs13
  :: forall p. KnownNat p => VS.Vector Field -> VS.Vector Field
permuteFlatLegs13 v =
  VS.generate (VS.length v) $ \k ->
    let ki = fromIntegral k
        vp = vpDim @p
        s1 = ki `mod` vp
        k1 = ki `div` vp
        s2 = k1 `mod` vp
        s3 = k1 `div` vp
    in v VS.! flatIndex3 vp s3 s2 s1

-- | @(C 1 ⊗ C p) +> Bond@ from the stored @C p +> Bond@ left site.
leftTransfer
  :: forall p. KnownNat p => LeftSite p -> (C 1 ⊗ C p) +> Bond
leftTransfer (LeftSite l) = l . lunit @(C p)

-- | @(Bond ⊗ C p) +> Bond@ from the stored @Bond +> (C p ⊗ Bond)@ bulk site.
bulkTransfer
  :: forall p. KnownNat p => BulkSite p -> (Bond ⊗ C p) +> Bond
bulkTransfer site =
  uncurryLinearMap -+$=> bulkCurried site
  where
    bulkCurried :: BulkSite p -> Bond +> (C p +> Bond)
    bulkCurried bulkSite =
      arr $
        LinearFunction $ \bond ->
          arr $ LinearFunction $ \phys -> applyBulkBondPhys bulkSite bond phys

-- | @(Bond ⊗ C p) +> C 1@ from the stored @Bond +> C p@ right site.
rightTransfer
  :: forall p. KnownNat p => RightSite p -> (Bond ⊗ C p) +> C 1
rightTransfer site =
  uncurryLinearMap -+$=> rightCurried site
  where
    rightCurried :: RightSite p -> Bond +> (C p +> C 1)
    rightCurried (RightSite r) =
      arr $
        LinearFunction $ \bond ->
          arr $ LinearFunction $ \phys -> (phys <.> (r $ bond)) *^ one1

-- | Whole chain as @(((C 1 ⊗ C p) ⊗ C p) ⊗ C p) +> C 1@ on growable 'Bond' bonds.
mpsChainMap
  :: forall p.
     ( KnownNat p, KnownNat (p * p), KnownNat (p * p * p) )
  => MPS p -> ((((C 1 ⊗ C p) ⊗ C p) ⊗ C p) +> C 1)
mpsChainMap mps =
  withMPS3 mps $ \l c r ->
    rightTransfer @p r
      . ((bulkTransfer @p c . (leftTransfer @p l ⊗^ idC @p)) ⊗^ idC @p)

-- | Closed physical tensor before @s₁ ↔ s₃@ leg reordering (see 'physicalFromClosedLegs').
mpsChainClose
  :: forall p.
     ( KnownNat p, KnownNat (p * p), KnownNat (p * p * p) )
  => MPS p -> Physical3 p
mpsChainClose mps =
  ( rassocMap
  . ((lunit ⊗^ idC @p) ⊗^ idC @p)
  . transposeMap (mpsChainMap mps)
  )
    $ one1
