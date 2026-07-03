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
{-# LANGUAGE NoStarIsType #-}

-- | Three-site MPS with abstract @LinearSpace@ operands and heterogeneous
-- boundary sites. Open boundaries use @Scalar bond@ as the unit object.
--
-- 'siteDagger' is categorical in 'TensorNetwork.Dagger' ('ApplicationTensorIso').
--
-- __Concrete @C n@ example:__ 'exampleMPSC22' and 'exampleMPSInnerC22' show that
-- 'mpsInner' only needs 'TransferCtx' (not 'PhysicalCtx' / 'toPhysicalMPS').
module TensorNetwork.MPS.Fixed3General
  ( LeftSite (..)
  , BulkSite (..)
  , RightSite (..)
  , MPS (..)
  , mps3
  , withMPS3
  , mpsConjugate
  , mpsInner
  , toPhysicalMPS
  , PhysicalTensor
  , leftInTransfer
  , SiteCtx
  , TransferCtx
  , MPSCtx
  , UnitSpace
  , UnitEnv
  , exampleMPSC22
  , exampleMPSInnerC22
  , exampleMPSInnerDemo
  , diagnoseExampleMPSInnerC22
  ) where

import Prelude hiding (id, ($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($), arr)
import Data.Complex (Complex)
import Data.Kind (Type)
import Data.VectorSpace (Scalar, InnerSpace ((<.>)))
import Control.Exception (SomeException, try, evaluate)
import Math.LinearMap.Category
  ( type (+>), type (⊗), TensorProduct, Tensor (..), (⊗)
  , TensorSpace, LinearSpace, HilbertSpace, DualVector
  , trace, (-+$>), LinearMap (LinearMap), getLinearMap
  , LinearFunction, pattern LinearFunction )
import Numeric.LinearAlgebra.Static (M, extract)
import Unsafe.Coerce (unsafeCoerce)
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Coercion (uncurryLinearMap, (-+$=>))
import Math.OrphanInstances ()
import Control.Category.Constrained (id)
import GHC.TypeLits (KnownNat)
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, Sized (fromList))
import Math.LinearMap.Category.Backend.HMatrix ()
import TensorNetwork.MPS.Fixed3.Internal (basis)
import TensorNetwork.MPS.LinmapStorage (linMapFromColumnImages, siteLinFromRows)
import TensorNetwork.Categorical
  ( (⊗^), conjugateMap, BoundaryUnit (..), lunitScalarLeg, lunitScalarLegInv, lunitAt, rassocMap
  , splitBond )
import TensorNetwork.Dagger
  ( siteDagger, ApplicationTensorIso, ApplicationFlat, ConjugateFlat
  , transposeMapSelfDual )

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
  , DualVector (ApplicationFlat bond phys) ~ ApplicationFlat bond phys
  , LinearSpace (ApplicationFlat bond phys)
  , DualVector (ApplicationFlat (Scalar bond) phys) ~ ApplicationFlat (Scalar bond) phys
  , Scalar (ApplicationFlat bond phys) ~ Field
  , Scalar (ApplicationFlat (Scalar bond) phys) ~ Field
  )

type MPSCtx bond phys = TransferCtx bond phys

-- | Three-site physical Hilbert space (right-nested tensor product of legs).
type PhysicalTensor phys = phys ⊗ (phys ⊗ phys)

-- | Left-nested chain domain of 'mpsChainMap'.
type ChainDomain bond phys = (((Scalar bond ⊗ phys) ⊗ phys) ⊗ phys)

-- | Extra constraints for closing the chain to 'PhysicalTensor'.
type PhysicalCtx bond phys =
  ( TransferCtx bond phys
  , DualVector (Scalar bond) ~ Scalar bond
  , DualVector (ChainDomain bond phys) ~ ChainDomain bond phys
  , TensorSpace (phys ⊗ phys)
  , TensorSpace (phys ⊗ (phys ⊗ phys))
  , TensorSpace ((bond ⊗ phys) ⊗ phys)
  , TensorSpace (((Scalar bond ⊗ phys) ⊗ phys) ⊗ phys)
  , LinearSpace (phys ⊗ phys)
  , LinearSpace (phys ⊗ (phys ⊗ phys))
  , HilbertSpace (phys ⊗ phys)
  , HilbertSpace (phys ⊗ (phys ⊗ phys))
  )

mpsChainMap
  :: forall bond phys. PhysicalCtx bond phys
  => MPS bond phys
  -> ((((Scalar bond ⊗ phys) ⊗ phys) ⊗ phys) +> Scalar bond)
mpsChainMap mps =
  withMPS3 mps $ \l c r ->
    let physId = Cat.id :: phys +> phys
    in rightInTransfer r
         . ((bulkLin c . (leftInTransfer l ⊗^ physId)) ⊗^ physId)

-- | Categorical map from an open-boundary MPS to its physical state
-- @|ψ(s₁,s₂,s₃)⟩@ as @phys ⊗ (phys ⊗ phys)@.
toPhysicalMPS
  :: forall bond phys. PhysicalCtx bond phys
  => MPS bond phys -> PhysicalTensor phys
toPhysicalMPS mps =
  ( rassocMap
      . ((lunitAt @(Scalar bond) @phys ⊗^ (id :: phys +> phys)) ⊗^ (id :: phys +> phys))
      . transposeMapSelfDual (mpsChainMap mps) )
    $ unitVector @(Scalar bond)

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

transferLeftSite
  :: forall bond phys. TransferCtx bond phys
  => LeftSite bond phys
  -> LeftSite bond phys
  -> UnitEnv bond
  -> TransferEnv bond
transferLeftSite bra ket env =
  let physId = Cat.id :: phys +> phys
  in leftInTransfer @bond ket . (env ⊗^ physId) . siteDagger (leftInTransfer @bond bra)

transferBulkSite
  :: forall bond phys. TransferCtx bond phys
  => BulkSite bond phys
  -> BulkSite bond phys
  -> TransferEnv bond
  -> TransferEnv bond
transferBulkSite (BulkSite bra) (BulkSite ket) env =
  let physId = Cat.id :: phys +> phys
  in ket . (env ⊗^ physId) . siteDagger bra

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

--------------------------------------------------------------------------------
-- Concrete @C 2@ example ('TransferCtx' only — no 'PhysicalCtx')
--------------------------------------------------------------------------------

-- | @2×2@ identity on @C 2@ (column images = standard basis).
idC2 :: C 2 +> C 2
idC2 = linMapFromColumnImages @2 @2 [basis @2 0, basis @2 1]

-- | A small hand-built @MPS (C 2) (C 2)@ for smoke tests.
--
-- Left boundary: 'leftLin = id' so 'leftInTransfer = lunitScalarLeg' (scalar leg
-- absorption). Bulk uses the same column storage as 'TensorNetwork.MPS.Fixed3'.
exampleMPSC22 :: MPS (C 2) (C 2)
exampleMPSC22 =
  mps3
    (LeftSite idC2)
    (BulkSite bulkTransfer)
    (RightSite idC2)
  where
    bulkTransfer :: (C 2 ⊗ C 2) +> C 2
    bulkTransfer = siteLinFromRows @2 @2 @2 bulkRows

    bulkRows :: [C 2]
    bulkRows = replicate 4 (fromList [0, 0])

-- | ⟨ψ|ψ⟩ for 'exampleMPSC22' — exercises the full transfer fold at @C 2@.
exampleMPSInnerC22 :: Field
exampleMPSInnerC22 = mpsInner exampleMPSC22 exampleMPSC22

-- | Print the concrete inner product (for REPL / smoke scripts).
exampleMPSInnerDemo :: IO ()
exampleMPSInnerDemo = diagnoseExampleMPSInnerC22 >> putStrLn ("⟨ψ|ψ⟩ = " ++ show exampleMPSInnerC22)

-- | Step through 'exampleMPSC22' / 'mpsInner' and report where evaluation fails.
diagnoseExampleMPSInnerC22 :: IO ()
diagnoseExampleMPSInnerC22 =
  withMPS3 exampleMPSC22 $ \l b r -> do
    putStrLn "=== Fixed3General mpsInner @C2 diagnostic ==="
    reportMat @2 @4 "bulkLin" (bulkLin b)
    reportMat @1 @4 "rightInTransfer ∘ splitBond" (rightInTransfer r . splitBondIso)
    reportMat @2 @2 "leftInTransfer ∘ lunitScalarLegInv (= idC2)" (leftInTransfer l . lunitScalarLegInv @(C 2))
    tryStep "siteDagger (leftInTransfer)" $
      getLinearMap (siteDagger (leftInTransfer l) :: C 2 +> (Field ⊗ C 2)) `seq` ()
    tryStep "transferLeftSite" $
      getLinearMap (transferLeftSite l l (Cat.id :: UnitEnv (C 2)) :: TransferEnv (C 2)) `seq` ()
    tryStep "left+bulk transfer" $
      let envL = transferLeftSite l l (Cat.id :: UnitEnv (C 2)) :: TransferEnv (C 2)
      in getLinearMap (transferBulkSite b b envL) `seq` ()
    tryStep "foldTransferInner (no trace)" $
      getLinearMap (foldTransferInner exampleMPSC22 exampleMPSC22 :: UnitEnv (C 2)) `seq` ()
    tryStep "full mpsInner" exampleMPSInnerC22
  where
    splitBondIso :: C 4 +> (C 2 ⊗ C 2)
    splitBondIso = splitBond @2 @2 @(C 2) @(C 2) @(C 4)

    reportMat :: forall r c w v.
      (KnownNat r, KnownNat c, Scalar v ~ Field, Scalar w ~ Field)
      => String -> (v +> w) -> IO ()
    reportMat label f =
      let m = unsafeCoerce (getLinearMap f) :: M r c
      in putStrLn $ label ++ ": M " ++ show (extract m)

    tryStep name action =
      try (evaluate action) >>= printResult name
    printResult :: Show a => String -> Either SomeException a -> IO ()
    printResult name (Left e) = putStrLn $ "FAIL " ++ name ++ ": " ++ show e
    printResult name (Right v) = putStrLn $ "OK   " ++ name ++ ": " ++ show v
