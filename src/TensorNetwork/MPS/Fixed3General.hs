{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Three-site MPS with abstract @LinearSpace@ operands and heterogeneous
-- boundary sites. Open boundaries use @Scalar bond@ as the unit object.
--
-- 'siteDagger' is categorical in 'TensorNetwork.Dagger' ('ApplicationTensorIso').
module TensorNetwork.MPS.Fixed3General
  ( LeftSite (..)
  , BulkSite (..)
  , RightSite (..)
  , MPS (..)
  , mps3
  , withMPS3
  , mpsConjugate
  , mpsInner
  , leftInTransfer
  , SiteCtx
  , TransferCtx
  , MPSCtx
  , UnitSpace
  , UnitEnv
  ) where

import Prelude hiding (id, ($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($), arr)
import Data.Complex (Complex)
import Data.Kind (Type)
import Data.VectorSpace (Scalar, InnerSpace ((<.>)))
import Math.LinearMap.Category
  ( type (+>), type (⊗), TensorProduct
  , TensorSpace, LinearSpace, FiniteDimensional, HilbertSpace, DualVector
  , LinearFunction, pattern LinearFunction
  , trace, (-+$>) )
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Coercion (uncurryLinearMap, (-+$=>))
import Math.OrphanInstances ()
import TensorNetwork.Categorical
  ( (⊗^), conjugateMap, BoundaryUnit (..), lunitScalarLeg )
import TensorNetwork.Dagger
  ( siteDagger, ApplicationTensorIso, ApplicationFlat, ConjugateFlat )

type Field = Complex Double

-- | Left boundary: physical leg only (@phys +> bond@; no incoming bond).
newtype LeftSite (bond :: Type) (phys :: Type) = LeftSite
  { leftLin :: phys +> bond }

-- | Bulk site in transfer orientation: @(bond ⊗ phys) +> bond@.
newtype BulkSite (bond :: Type) (phys :: Type) = BulkSite
  { bulkLin :: (bond ⊗ phys) +> bond }

-- | Right boundary: no outgoing bond (@bond +> phys@).
newtype RightSite (bond :: Type) (phys :: Type) = RightSite
  { rightLin :: bond +> phys }

-- | Open-boundary three-site MPS (@left + bulk + right@).
data MPS (bond :: Type) (phys :: Type) = MPS
  { mpsLeft :: LeftSite bond phys
  , mpsBulk :: BulkSite bond phys
  , mpsRight :: RightSite bond phys
  }

mps3
  :: LeftSite bond phys
  -> BulkSite bond phys
  -> RightSite bond phys
  -> MPS bond phys
mps3 = MPS

withMPS3
  :: MPS bond phys
  -> (LeftSite bond phys -> BulkSite bond phys -> RightSite bond phys -> a)
  -> a
withMPS3 (MPS l c r) k = k l c r

-- | Constraints shared by all three site shapes on the same operands.
type SiteCtx bond phys =
  ( TensorSpace bond, TensorSpace phys
  , LinearSpace bond, LinearSpace phys
  , FiniteDimensional bond, FiniteDimensional phys
  , FiniteDimensional (Scalar bond)
  , LinearSpace (Scalar bond)
  , HilbertSpace bond, HilbertSpace phys
  , DualVector bond ~ bond
  , Scalar bond ~ Field, Scalar phys ~ Field
  )

-- | Monoidal unit at open boundaries: the scalar field of the bond spaces.
type UnitSpace bond = Scalar bond

-- | Environment map at the open boundary (@Scalar bond +> Scalar bond@).
type UnitEnv bond = UnitSpace bond +> UnitSpace bond

-- | Bond environment carried through the bulk transfer step.
type TransferEnv bond = bond +> bond

-- | Constraints for transfer contraction (@⊗^@, 'siteDagger', scalar unit leg).
type TransferCtx bond phys =
  ( SiteCtx bond phys
  , Scalar bond ~ Scalar phys
  , BoundaryUnit (Scalar bond)
  , TensorSpace (Scalar bond ⊗ phys)
  , TensorProduct (Scalar bond) phys ~ phys
  , ApplicationTensorIso bond phys
  , ApplicationTensorIso (Scalar bond) phys
  , ConjugateFlat (ApplicationFlat bond phys) bond
  , ConjugateFlat (ApplicationFlat bond phys) (Scalar bond)
  , ConjugateFlat (ApplicationFlat (Scalar bond) phys) bond
  , FiniteDimensional (ApplicationFlat bond phys)
  , FiniteDimensional (ApplicationFlat (Scalar bond) phys)
  , DualVector (ApplicationFlat bond phys) ~ ApplicationFlat bond phys
  , DualVector (ApplicationFlat (Scalar bond) phys) ~ ApplicationFlat (Scalar bond) phys
  , Scalar (ApplicationFlat bond phys) ~ Field
  , Scalar (ApplicationFlat (Scalar bond) phys) ~ Field
  )

type MPSCtx bond phys = TransferCtx bond phys

-- | Left site in transfer orientation: @(Scalar bond ⊗ phys) +> bond@.
leftInTransfer
  :: forall bond phys. TransferCtx bond phys
  => LeftSite bond phys -> (Scalar bond ⊗ phys) +> bond
leftInTransfer (LeftSite f) = f . lunitScalarLeg @phys

-- | Right site in transfer orientation: @(bond ⊗ phys) +> Scalar bond@.
rightInTransfer
  :: forall bond phys. TransferCtx bond phys
  => RightSite bond phys -> (bond ⊗ phys) +> Scalar bond
rightInTransfer (RightSite r) =
  uncurryLinearMap -+$=> rightCurried
  where
    rightCurried :: bond +> (phys +> Scalar bond)
    rightCurried =
      arr $
        LinearFunction $ \bond ->
          arr $
            LinearFunction $ \phys ->
              unscalarizeUnit @Field $ (phys <.> (r $ bond))

conjugateLeftSite :: SiteCtx bond phys => LeftSite bond phys -> LeftSite bond phys
conjugateLeftSite (LeftSite f) = LeftSite (conjugateMap f)

conjugateBulkSite :: SiteCtx bond phys => BulkSite bond phys -> BulkSite bond phys
conjugateBulkSite (BulkSite f) = BulkSite (conjugateMap f)

conjugateRightSite :: SiteCtx bond phys => RightSite bond phys -> RightSite bond phys
conjugateRightSite (RightSite f) = RightSite (conjugateMap f)

mpsConjugate :: SiteCtx bond phys => MPS bond phys -> MPS bond phys
mpsConjugate (MPS l c r) =
  MPS (conjugateLeftSite l) (conjugateBulkSite c) (conjugateRightSite r)

-- | One transfer update at the left boundary (bra site is already conjugated).
--
-- @ket ∘ (env ⊗^ id) ∘ siteDagger bra@ on transfer-oriented left sites.
transferLeftSite
  :: forall bond phys. TransferCtx bond phys
  => LeftSite bond phys
  -> LeftSite bond phys
  -> UnitEnv bond
  -> TransferEnv bond
transferLeftSite bra ket env =
  let physId = Cat.id :: phys +> phys
  in leftInTransfer @bond ket . (env ⊗^ physId) . siteDagger (leftInTransfer @bond bra)

-- | One transfer update at a bulk site (bra site is already conjugated).
--
-- @ket ∘ (env ⊗^ id) ∘ siteDagger bra@ — bulk sites are already in transfer
-- orientation @(bond ⊗ phys) +> bond@.
transferBulkSite
  :: forall bond phys. TransferCtx bond phys
  => BulkSite bond phys
  -> BulkSite bond phys
  -> TransferEnv bond
  -> TransferEnv bond
transferBulkSite (BulkSite bra) (BulkSite ket) env =
  let physId = Cat.id :: phys +> phys
  in ket . (env ⊗^ physId) . siteDagger bra

-- | One transfer update at the right boundary (bra site is already conjugated).
--
-- @ket ∘ (env ⊗^ id) ∘ siteDagger bra@ on transfer-oriented right sites.
transferRightSite
  :: forall bond phys. TransferCtx bond phys
  => RightSite bond phys
  -> RightSite bond phys
  -> TransferEnv bond
  -> UnitEnv bond
transferRightSite bra ket env =
  let physId = Cat.id :: phys +> phys
  in rightInTransfer ket . (env ⊗^ physId) . siteDagger (rightInTransfer bra)

foldTransferInner
  :: forall bond phys. TransferCtx bond phys
  => MPS bond phys -> MPS bond phys -> UnitEnv bond
foldTransferInner (MPS lB bB rB) (MPS lK bK rK) =
  let env0 = Cat.id :: UnitEnv bond
  in transferRightSite @bond @phys rB rK $
       transferBulkSite @bond @phys bB bK $
         transferLeftSite @bond @phys lB lK env0

-- | MPS inner product ⟨ψ|φ⟩: transfer fold from the identity boundary
-- environment, closed with 'trace'.
mpsInner
  :: forall bond phys. TransferCtx bond phys
  => MPS bond phys -> MPS bond phys -> Scalar bond
mpsInner psi phi =
  trace @(Scalar bond) -+$> foldTransferInner @bond @phys (mpsConjugate psi) phi

instance Show (LeftSite bond phys) where show _ = "LeftSite"
instance Show (BulkSite bond phys) where show _ = "BulkSite"
instance Show (RightSite bond phys) where show _ = "RightSite"
instance Show (MPS bond phys) where show _ = "MPS"
