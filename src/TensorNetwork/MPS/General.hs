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
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedLists #-}
{- HLINT ignore "Redundant $" -}

-- | Three-site MPS with abstract @LinearSpace@ operands and heterogeneous
-- boundary sites. Open boundaries use @Scalar bond@ as the unit object.
--
-- 'siteDagger' is categorical in 'TensorNetwork.Dagger' ('ApplicationTensorIso').
--
-- __Concrete @C n@ example:__ 'exampleMPSC22' and 'exampleMPSInnerC22' show that
-- 'mpsInner' only needs 'TransferCtx' (not 'PhysicalCtx' / 'toPhysicalMPS').
module TensorNetwork.MPS.General where

import Prelude hiding (id, ($), (.))
import qualified Control.Category.Constrained as Cat
import Control.Category.Constrained ((.))
import Control.Arrow.Constrained (($), arr)
import Data.Complex (Complex ((:+)))
import Control.Monad (replicateM)
import qualified Test.QuickCheck as QC
import Data.Kind (Type)
import Data.VectorSpace (InnerSpace ((<.>)))
import Math.LinearMap.Category
  ( type (+>), type (⊗), TensorProduct, Tensor (..), (⊗)
  , TensorSpace (..), LinearSpace (..), HilbertSpace, DualVector
  , trace, (-+$>), LinearMap (LinearMap), getLinearMap
  , LinearFunction, pattern LinearFunction, DimensionAware (..), LSpace, adjoint, Norm (..), type (-+>), getAntilinearFunction, lfun, SemilinearFunction (SemilinearFunction), VectorSpace (..), Num' )
import Numeric.LinearAlgebra.Static (Sized (konst))
import Math.LinearMap.Category.Instances ()
import Math.OrphanInstances ()
import Control.Category.Constrained (id)
import GHC.TypeLits (KnownNat, type (*), type (<=), type (-), type (+))
import Numeric.LinearAlgebra.Static.COrphans ()
import Numeric.LinearAlgebra.Static (C, Sized (fromList))
import Math.LinearMap.Category.Backend.HMatrix ()
import TensorNetwork.MPS.LinmapStorage
import TensorNetwork.Categorical
  ( (⊗^)
   )
import Data.Coerce (coerce)
import qualified Debug.Trace as Debug
import Math.LinearMap.Asserted (flipBilin)
import GHC.TypeNats (natVal)
import Data.Data (Proxy(..))
import GHC.TypeLits (Nat)
import Linear.V (V (..), Finite (..))
import Control.Lens ((^.), Ixed (ix), (^?), _1, _2)
import Data.Maybe (fromMaybe)
import Linear (V1(..))
import Data.Foldable (Foldable(toList))
import qualified Data.Vector as Vector
import Data.VectorSpace.Free (FinSuppSeq(..))
import Data.VectorSpace.Free.FiniteSupportedSequence
import qualified Data.Vector.Unboxed as U
import Random.Arbitrary
-- currently broken because of sesquilinearity of complex metric
data FullNorm v = FullNorm {lower :: v -+> DualVector v, raise :: DualVector v -+> v}


type PhysicalTensor phys = OTimes 3 phys

type family OTimes (n :: Nat) (phys :: Type) :: Type where
  OTimes 0 phys = ()
  OTimes 1 phys = phys
  OTimes n phys = phys ⊗ OTimes (n - 1) phys

type LeftSite (bond :: Type) (phys :: Type) = phys +> bond
type BulkSite (bond :: Type) (phys :: Type) = (bond ⊗ phys) +> bond
type RightSite (bond :: Type) (phys :: Type) = bond +> phys

-- | Open-boundary three-site MPS (@left + bulk + right@).
data MPS (bond :: Type) (phys :: Type) (n :: Nat) = MPS
  { mpsLeft :: phys +> bond
  , mpsBulk :: V n ((bond ⊗ phys) +> bond)
  , mpsRight :: bond +> phys
  }

data MPO (bond :: Type) (phys :: Type) (n :: Nat) = MPO
  { mpoLeft :: phys +> (bond ⊗ phys)
  , mpoBulk :: V n ((bond ⊗ phys) +> (bond ⊗ phys))
  , mpoRight :: (bond ⊗ phys) +> phys
  }

type MPSConstraints bond phys = (LSpace phys, LSpace bond, InnerSpace phys, Scalar bond ~ Complex Double, Scalar (DualVector bond) ~ Complex Double, Scalar (DualVector phys) ~ Complex Double,  Scalar phys ~ Complex Double, DualVector (DualVector bond) ~ bond, DualVector (DualVector phys) ~ phys, LinearSpace (DualVector bond), LinearSpace (DualVector phys), InnerSpace bond)


hermitianNorm :: (LinearSpace v, v ~ DualVector v) => FullNorm v
hermitianNorm = FullNorm {
  lower = lfun (getAntilinearFunction vectorConjugate),
  raise = lfun (getAntilinearFunction vectorConjugate)
}

dagger :: forall v w. (LSpace v, LSpace w, LSpace (DualVector v), LSpace (DualVector w), Scalar v ~ Scalar w, Scalar (DualVector v) ~ Scalar w, Scalar (DualVector w) ~ Scalar w, DualVector (DualVector w) ~ w) => FullNorm w -> FullNorm v ->  (v +> w) -> (w +> v)
dagger nb nv  (LinearMap f)  = arr (raise nv . arr lm . lower nb) where
  tensor = transposeTensor $ coerce f :: DualVector (DualVector w) ⊗ DualVector v
  lm = coerce tensor :: DualVector w +> DualVector v

siteDagger :: forall u v w. (LSpace v, LSpace w, LSpace u, LSpace (DualVector v), LSpace (DualVector w), Scalar v ~ Scalar w, Scalar (DualVector v) ~ Scalar w, Scalar (DualVector w) ~ Scalar w, DualVector (DualVector w) ~ w, Scalar u ~ Scalar w, Scalar (DualVector u) ~ Scalar w, LinearSpace (DualVector u)) => FullNorm w -> FullNorm v -> FullNorm u -> ((u ⊗ v) +> w)  -> (w +> (u ⊗ v))
siteDagger nw nv nu = dagger nw (tensorNorm nu nv)

tensorNorm :: forall v w . (LSpace v, LSpace w, Scalar v ~ Scalar w, Scalar (DualVector w) ~ Scalar w, Scalar (DualVector v) ~ Scalar w, LinearSpace (DualVector v), LinearSpace (DualVector w)) => FullNorm v -> FullNorm w -> FullNorm (v ⊗ w)
tensorNorm nv nw = FullNorm {
  lower =
    LinearFunction (\x -> let
      du = (arr (lower nv) ⊗^ arr (lower nw)) :: (v ⊗ w) +> (DualVector v ⊗ DualVector w)
    in coerce (du $ x)),
  raise =
    LinearFunction (\x -> let
    y = coerce x :: DualVector v ⊗ DualVector w
    du =  (arr (raise $ nv) ⊗^ arr (raise $ nw)) :: (DualVector v ⊗ DualVector w) +> (v ⊗ w)
    in du $ y)
    }

toTensorWithNorm ::forall  phys. (LSpace phys, Scalar phys ~ Complex Double, LSpace (DualVector phys), Scalar (DualVector phys) ~ Complex Double, DualVector (DualVector phys) ~ phys) => (DualVector phys -+> phys) -> (phys +> phys) -+> ( phys ⊗ phys)
toTensorWithNorm lw = LinearFunction coerce . (flipBilin composeLinear -+$> arr lw)

bulkToMap :: forall bond phys. (MPSConstraints bond phys) => BulkSite bond phys -> bond +> (phys +> bond)
bulkToMap f = arr (lfun coerce :: (DualVector phys ⊗ bond) -+> ( phys +> bond)) . coerce f

toPhysicalMPS :: forall bond phys . (MPSConstraints bond phys) => FullNorm phys -> MPS bond phys 1 -> OTimes 3 phys
toPhysicalMPS (FullNorm _ lw) mps = (fmapTensor -+$> toTensorWithNorm lw)
 $ coerce (
  postCompose (mpsRight mps)
  . bulkToMap (mpsBulk mps ^. _1)
  .  mpsLeft mps
  . arr lw
  )

postCompose :: (Scalar  v ~ Scalar w, LinearSpace w, LinearSpace v, Num' (Scalar w)) => (v +> w) -> (w +> v) +> (w +> w)
postCompose f = arr (composeLinear -+$> f)

transferLeftSite
  :: forall bond phys. MPSConstraints bond phys =>
  FullNorm bond -> FullNorm phys ->
  LeftSite bond phys
  -> LeftSite bond phys
  -> (bond +> bond)
transferLeftSite nb np bra ket = ket . dagger nb np bra

transferBulkSite
  :: forall bond phys. MPSConstraints bond phys =>
  FullNorm bond -> FullNorm phys ->
  BulkSite bond phys
  -> BulkSite bond phys
  -> (bond +> bond)
  -> (bond +> bond)
transferBulkSite nb np bra ket env = ket . (env ⊗^ Cat.id) .  siteDagger nb np nb bra

transferRightSite
  :: forall bond phys.
  (MPSConstraints bond phys) =>
  FullNorm bond -> FullNorm phys ->
  RightSite bond phys
  -> RightSite bond phys
  -> (bond +> bond)
  -> Scalar bond
transferRightSite nb np bra ket env = trace $ (env . dagger np nb  ket . bra)

mpsInner
  :: forall bond phys (n :: Nat).
  MPSConstraints bond phys =>
  FullNorm bond -> FullNorm phys -> MPS bond phys n -> MPS bond phys n -> Scalar bond
mpsInner nb np (MPS lB bB rB) (MPS lK bK rK) =
  transferRightSite nb np rB rK $ transferBulk $ transferLeftSite nb np lB lK where

    transfers = uncurry (transferBulkSite nb np) <$> zip (toList bB) (toList bK)
    transferBulk = foldr (.) Cat.id transfers

instance (KnownNat n, KnownNat m, KnownNat (m*n), KnownNat (n*m), vb ~ C n, vp ~ C m, KnownNat q) => Show (MPS vb vp q) where show (MPS l b r) = "MPS: Left site is: " ++ show (getLinearMap l) ++ " \nBulk site is: " ++ show (getLinearMap <$>  b) ++ " \nRight site is: " ++ show (getLinearMap r)

mpsMPOContraction
  :: forall bond phys (n :: Nat).
  MPSConstraints bond phys =>
  FullNorm bond -> FullNorm phys -> MPO bond phys n -> MPS bond phys n -> MPO bond phys n
mpsMPOContraction nb np (MPO lB bB rB) (MPS lK bK rK) = undefined


-- | Print the concrete inner product (for REPL / smoke scripts).
-- exampleMPSInnerDemo :: IO ()
-- exampleMPSInnerDemo = diagnoseExampleMPSInnerC22 >> putStrLn ("⟨ψ|ψ⟩ = " ++ show exampleMPSInnerC22)

-- | Step through 'exampleMPSC22' / 'mpsInner' and report where evaluation fails.
-- diagnoseExampleMPSInnerC22 :: IO ()
-- diagnoseExampleMPSInnerC22 =
--   withMPS3 exampleMPSC22 $ \l b r -> do
--     putStrLn "=== FixedGeneral mpsInner @C2 diagnostic ==="
--     reportMat @2 @4 "bulkLin" (bulkLin b)
--     reportMat @1 @4 "rightInTransfer ∘ splitBond" (rightInTransfer r . splitBondIso)
--     reportMat @2 @2 "leftInTransfer ∘ lunitScalarLegInv (= idC2)" (leftInTransfer l . lunitScalarLegInv @(C 2))
--     tryStep "siteDagger (leftInTransfer)" $
--       getLinearMap (siteDagger (leftInTransfer l) :: C 2 +> (Field ⊗ C 2)) `seq` ()
--     tryStep "transferLeftSite" $
--       getLinearMap (transferLeftSite l l (Cat.id :: UnitEnv (C 2)) :: TransferEnv (C 2)) `seq` ()
--     tryStep "left+bulk transfer" $
--       let envL = transferLeftSite l l (Cat.id :: UnitEnv (C 2)) :: TransferEnv (C 2)
--       in getLinearMap (transferBulkSite b b envL) `seq` ()
--     tryStep "foldTransferInner (no trace)" $
--       getLinearMap (foldTransferInner exampleMPSC22 exampleMPSC22 :: UnitEnv (C 2)) `seq` ()
--     tryStep "full mpsInner" exampleMPSInnerC22
--   where
--     splitBondIso :: C 4 +> (C 2 ⊗ C 2)
--     splitBondIso = splitBond @2 @2 @(C 2) @(C 2) @(C 4)

--     reportMat :: forall r c w v.
--       (KnownNat r, KnownNat c, Scalar v ~ Field, Scalar w ~ Field)
--       => String -> (v +> w) -> IO ()
--     reportMat label f =
--       let m = unsafeCoerce (getLinearMap f) :: M r c
--       in putStrLn $ label ++ ": M " ++ show (extract m)

--     tryStep name action =
--       try (evaluate action) >>= printResult name
--     printResult :: Show a => String -> Either SomeException a -> IO ()
--     printResult name (Left e) = putStrLn $ "FAIL " ++ name ++ ": " ++ show e
--     printResult name (Right v) = putStrLn $ "OK   " ++ name ++ ": " ++ show v



  -- where
  --   bulkTransfer :: (C 2 ⊗ C 2) +> C 2
  --   bulkTransfer = siteLinFromRows @2 @2 @2 bulkRows

  --   bulkRows :: [C 2]
  --   bulkRows = replicate 4 (fromList [0, 0])


-- step1 = transferLeftSite (FullNorm id id) (FullNorm id id) (mpsLeft exampleMPSC22) (mpsLeft exampleMPSC22) Cat.id
-- step2 = transferBulkSite' (FullNorm id id) (FullNorm id id) (mpsBulk exampleMPSC22) (mpsBulk exampleMPSC22) step1


-- transferBulkSite'
--   :: FullNorm (C 2) -> FullNorm (C 2) ->
--   BulkSite (C 2) (C 2)
--   -> BulkSite (C 2) (C 2)
--   -> ((C 2) +> (C 2))
--   -> ((C 2) +> (C 2))
-- transferBulkSite' nb np (BulkSite bra) (BulkSite ket) env = 
--   -- ket . (env ⊗^ Cat.id) .  (trace' "tbD" $ siteDagger nb np nb (trace' ("bra") $ bra))
--   ket . (env ⊗^ Cat.id) .  (trace'' $ siteDagger' nb np nb $ Debug.trace ("trace a " ++ show (getLinearMap bra)) bra)
--   -- env


-- -- dagger :: forall v w. (LSpace v, LSpace w, LSpace (DualVector v), LSpace (DualVector w), Scalar v ~ Scalar w, Scalar (DualVector v) ~ Scalar w, Scalar (DualVector w) ~ Scalar w, DualVector (DualVector w) ~ w) => FullNorm w -> FullNorm v ->  (v +> w) -> (w +> v)
-- dagger' :: FullNorm (C 2) -> FullNorm (C 2 ⊗ C 2) ->  ((C 2 ⊗ C 2) +> (C 2)) -> ((C 2) +> (C 2 ⊗ C 2))
-- dagger' nb nv  f = arr (LinearFunction (\x -> raise nv $ lm $ lower nb $ x) ) where
--   tensor = getAntilinearFunction vectorConjugate $ transposeTensor $ coerce f :: DualVector (DualVector (C 2)) ⊗ DualVector (C 2 ⊗ C 2)
--   lm = coerce tensor :: DualVector (C 2) +> DualVector (C 2 ⊗ C 2)
--   lm' = LinearFunction (\x -> LinearMap (konst 1)) :: DualVector (C 2) -+> DualVector (C 2 ⊗ C 2)
--   lm'' = arr lm' :: DualVector (C 2) +> DualVector (C 2 ⊗ C 2)

--     -- arr lm :: DualVector (C 2) -+> DualVector (C 2 ⊗ C 2)

-- siteDagger' :: FullNorm (C 2) -> FullNorm (C 2) -> FullNorm (C 2) -> ((C 2) ⊗ (C 2)) +> (C 2)  -> (C 2 +> ((C 2) ⊗ (C 2)))
-- siteDagger' nw nv nu f = dagger' nw (tensorNorm nu nv) f

-- tensorNorm' :: FullNorm (C 2) -> FullNorm (C 2) -> FullNorm ((C 2) ⊗ (C 2))
-- tensorNorm' nb np = FullNorm {
--   lower = 
--     LinearFunction (\x -> let 
--       du = (arr (lower nb) ⊗^ arr (lower np)) :: ((C 2) ⊗ (C 2)) +> (DualVector (C 2) ⊗ DualVector (C 2))
--     in coerce $ (du $ x)), 

--   raise = 
--     LinearFunction (\x -> let 
--     y = coerce x :: DualVector (C 2) ⊗ DualVector (C 2)
--     foo =  (arr (raise $ nb) ⊗^ arr (raise np)) :: (DualVector (C 2) ⊗ DualVector (C 2)) +> ((C 2) ⊗ (C 2))
--     in foo $ y) 
    -- }
