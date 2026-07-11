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
{- HLINT ignore "Redundant $" -}

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
  , mpsConjugate
  , mpsInner
  -- , toPhysicalMPS
  , PhysicalTensor
  , leftInTransfer
  -- , SiteCtx
  , exampleMPSC22
  , exampleMPSInnerC22
  -- , exampleMPSInnerDemo
  -- , diagnoseExampleMPSInnerC22
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
  , TensorSpace (..), LinearSpace, HilbertSpace, DualVector
  , trace, (-+$>), LinearMap (LinearMap), getLinearMap
  , LinearFunction, pattern LinearFunction, DimensionAware (..), LSpace, adjoint, Norm (..), type (-+>), getAntilinearFunction, lfun )
import Numeric.LinearAlgebra.Static (M, extract, Sized (konst))
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
import TensorNetwork.Dagger ( ApplicationTensorIso, ApplicationFlat, ConjugateFlat
  , transposeMapSelfDual )
import Data.Coerce (coerce)
import qualified Debug.Trace as Debug

data FullNorm v = FullNorm {raise :: v -+> DualVector v, lower :: DualVector v -+> v}

dagger :: forall v w. (LSpace v, LSpace w, LSpace (DualVector v), LSpace (DualVector w), Scalar v ~ Scalar w, Scalar (DualVector v) ~ Scalar w, Scalar (DualVector w) ~ Scalar w, DualVector (DualVector w) ~ w) => FullNorm w -> FullNorm v ->  (v +> w) -> (w +> v)
dagger nb nv  (LinearMap f)  = arr (lower nv . arr lm . raise nb) where
  tensor = getAntilinearFunction vectorConjugate $ transposeTensor $ coerce f :: DualVector (DualVector w) ⊗ DualVector v
  lm = coerce tensor :: DualVector w +> DualVector v

siteDagger :: forall u v w. (LSpace v, LSpace w, LSpace u, LSpace (DualVector v), LSpace (DualVector w), Scalar v ~ Scalar w, Scalar (DualVector v) ~ Scalar w, Scalar (DualVector w) ~ Scalar w, DualVector (DualVector w) ~ w, Scalar u ~ Scalar w, Scalar (DualVector u) ~ Scalar w, LinearSpace (DualVector u)) => FullNorm w -> FullNorm v -> FullNorm u -> ((u ⊗ v) +> w)  -> (w +> (u ⊗ v))
siteDagger nw nv nu = dagger nw (tNorm nu nv)

tNorm :: forall v w . (LSpace v, LSpace w, Scalar v ~ Scalar w, Scalar (DualVector w) ~ Scalar w, Scalar (DualVector v) ~ Scalar w, LinearSpace (DualVector v), LinearSpace (DualVector w)) => FullNorm v -> FullNorm w -> FullNorm (v ⊗ w)
tNorm nv nw = FullNorm {
  raise = 
    LinearFunction (\x -> let 
      du = (arr (raise nv) ⊗^ arr (raise nw)) :: (v ⊗ w) +> (DualVector v ⊗ DualVector w)
    in coerce (du $ x)), 
  lower = 
    LinearFunction (\x -> let 
    y = coerce x :: DualVector v ⊗ DualVector w
    du =  (arr (lower $ nv) ⊗^ arr (lower $ nw)) :: (DualVector v ⊗ DualVector w) +> (v ⊗ w)
    in du $ y) 
    }

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


-- | Three-site physical Hilbert space (right-nested tensor product of legs).
type PhysicalTensor phys = phys ⊗ (phys ⊗ phys)

-- | Left-nested chain domain of 'mpsChainMap'.
-- type ChainDomain bond phys = (((Scalar bond ⊗ phys) ⊗ phys) ⊗ phys)


-- mpsChainMap
--   :: forall bond phys. PhysicalCtx bond phys
--   => MPS bond phys
--   -> ((((Scalar bond ⊗ phys) ⊗ phys) ⊗ phys) +> Scalar bond)
-- mpsChainMap mps =
--   withMPS3 mps $ \l c r ->
--     let physId = Cat.id :: phys +> phys
--     in rightInTransfer r
--          . ((bulkLin c . (leftInTransfer l ⊗^ physId)) ⊗^ physId)

-- -- | Categorical map from an open-boundary MPS to its physical state
-- -- @|ψ(s₁,s₂,s₃)⟩@ as @phys ⊗ (phys ⊗ phys)@.
-- toPhysicalMPS
--   :: forall bond phys. PhysicalCtx bond phys
--   => MPS bond phys -> PhysicalTensor phys
-- toPhysicalMPS mps =
--   ( rassocMap
--       . ((lunitAt @(Scalar bond) @phys ⊗^ (id :: phys +> phys)) ⊗^ (id :: phys +> phys))
--       . transposeMapSelfDual (mpsChainMap mps) )
--     $ unitVector @(Scalar bond)

type MPSConstraints bond phys = (HilbertSpace phys, HilbertSpace bond, Scalar phys ~ Scalar bond,  Scalar (Scalar bond) ~ Scalar bond, LinearSpace (Scalar bond), Scalar (DualVector (Scalar bond)) ~ Scalar bond, DualVector (DualVector (Scalar bond)) ~ Scalar bond, LinearSpace (DualVector (Scalar bond)), DualVector (Scalar bond) ~ Scalar bond)

-- | Left site in transfer orientation: @(Scalar bond ⊗ phys) +> bond@.
leftInTransfer
  :: forall bond phys. 
  MPSConstraints bond phys => 
  LeftSite bond phys -> (Scalar bond ⊗ phys) +> bond
leftInTransfer (LeftSite f) = f . lunitScalarLeg @phys

-- | Right site in transfer orientation: @(bond ⊗ phys) +> Scalar bond@.
-- rightInTransfer
--   :: forall bond phys. 
--   MPSConstraints bond phys => 
--   RightSite bond phys -> (bond ⊗ phys) +> Scalar bond
-- rightInTransfer (RightSite r) = undefined
--   -- uncurryLinearMap -+$=> rightCurried
--   -- where
--   --   rightCurried :: bond +> (phys +> Scalar bond)
--   --   rightCurried =
--   --     arr $
--   --       LinearFunction $ \bond ->
--   --         arr $
--   --           LinearFunction $ \phys ->
--   --             unscalarizeUnit @Field $ (phys <.> (r $ bond))

conjugateLeftSite :: MPSConstraints bond phys => LeftSite bond phys -> LeftSite bond phys
conjugateLeftSite (LeftSite f) = LeftSite (conjugateMap f)

conjugateBulkSite :: MPSConstraints bond phys => BulkSite bond phys -> BulkSite bond phys
conjugateBulkSite (BulkSite f) = BulkSite (conjugateMap f)

conjugateRightSite :: MPSConstraints bond phys => RightSite bond phys -> RightSite bond phys
conjugateRightSite (RightSite f) = RightSite (conjugateMap f)

mpsConjugate :: MPSConstraints bond phys => MPS bond phys -> MPS bond phys
mpsConjugate (MPS l c r) =
  MPS (conjugateLeftSite l) (conjugateBulkSite c) (conjugateRightSite r)

transferLeftSite
  :: forall bond phys. MPSConstraints bond phys => 
  FullNorm bond -> FullNorm phys ->
  LeftSite bond phys
  -> LeftSite bond phys
  -> (bond +> bond)
transferLeftSite nb np (LeftSite bra) (LeftSite ket) = ket . (dagger nb np bra :: bond +> phys)

transferBulkSite
  :: forall bond phys. MPSConstraints bond phys => 
  FullNorm bond -> FullNorm phys ->
  BulkSite bond phys
  -> BulkSite bond phys
  -> (bond +> bond)
  -> (bond +> bond)
transferBulkSite nb np (BulkSite bra) (BulkSite ket) env = ket . (env ⊗^ Cat.id) .  siteDagger nb np nb bra

transferRightSite
  :: forall bond phys. 
  (MPSConstraints bond phys) =>
  FullNorm bond -> FullNorm phys ->
  RightSite bond phys
  -> RightSite bond phys
  -> (bond +> bond)
  -> Scalar bond
transferRightSite nb np (RightSite bra) (RightSite ket) env = trace $ (env . dagger np nb  ket . bra)

foldTransferInner
  :: forall bond phys. 
  MPSConstraints bond phys =>
  FullNorm bond -> FullNorm phys -> MPS bond phys -> MPS bond phys -> Scalar bond
foldTransferInner nb np (MPS lB bB rB) (MPS lK bK rK) =
  transferRightSite nb np rB rK $
       transferBulkSite nb np bB bK $
         transferLeftSite nb np lB lK

-- | MPS inner product ⟨ψ|φ⟩: transfer fold from the identity boundary
-- environment, closed with 'trace'.
mpsInner
  :: forall bond phys. 
  MPSConstraints bond phys =>
  FullNorm bond -> FullNorm phys -> MPS bond phys -> MPS bond phys -> Scalar bond
mpsInner nb np psi = foldTransferInner @bond @phys nb np (mpsConjugate psi)

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
  MPS
    (LeftSite { leftLin = idC2 })
    (BulkSite $ LinearMap (konst 1))
    (RightSite idC2)
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
-- dagger' nb nv  f = arr (LinearFunction (\x -> lower nv $ lm $ raise nb $ x) ) where
--   tensor = getAntilinearFunction vectorConjugate $ transposeTensor $ coerce f :: DualVector (DualVector (C 2)) ⊗ DualVector (C 2 ⊗ C 2)
--   lm = coerce tensor :: DualVector (C 2) +> DualVector (C 2 ⊗ C 2)
--   lm' = LinearFunction (\x -> LinearMap (konst 1)) :: DualVector (C 2) -+> DualVector (C 2 ⊗ C 2)
--   lm'' = arr lm' :: DualVector (C 2) +> DualVector (C 2 ⊗ C 2)
    
--     -- arr lm :: DualVector (C 2) -+> DualVector (C 2 ⊗ C 2)

-- siteDagger' :: FullNorm (C 2) -> FullNorm (C 2) -> FullNorm (C 2) -> ((C 2) ⊗ (C 2)) +> (C 2)  -> (C 2 +> ((C 2) ⊗ (C 2)))
-- siteDagger' nw nv nu f = dagger' nw (tNorm nu nv) f

-- tNorm' :: FullNorm (C 2) -> FullNorm (C 2) -> FullNorm ((C 2) ⊗ (C 2))
-- tNorm' nb np = FullNorm {
--   raise = 
--     LinearFunction (\x -> let 
--       du = (arr (raise nb) ⊗^ arr (raise np)) :: ((C 2) ⊗ (C 2)) +> (DualVector (C 2) ⊗ DualVector (C 2))
--     in coerce $ (du $ x)), 
  
--   lower = 
--     LinearFunction (\x -> let 
--     y = coerce x :: DualVector (C 2) ⊗ DualVector (C 2)
--     foo =  (arr (lower $ nb) ⊗^ arr (lower np)) :: (DualVector (C 2) ⊗ DualVector (C 2)) +> ((C 2) ⊗ (C 2))
--     in foo $ y) 
    -- }

trace' str f = Debug.trace ("trace'" ++ show str) $ f
trace'' f = Debug.trace ("trace''" ++ show (getLinearMap f)) $ f
trace''' f = Debug.trace ("trace'''" ++ show f) $ f
trace'''' f = Debug.trace ("trace''" ++ show (getTensorProduct f)) $ f

-- | ⟨ψ|ψ⟩ for 'exampleMPSC22' — exercises the full transfer fold at @C 2@.
exampleMPSInnerC22 :: Complex Double
exampleMPSInnerC22 = mpsInner (FullNorm id id ) (FullNorm id id ) exampleMPSC22 exampleMPSC22

exampleDaggerC2 :: C 2 +> C 2
exampleDaggerC2 = dagger (FullNorm id id) (FullNorm id id) idC2

exampleTNorm ::   (C 2 ⊗ C 4)
exampleTNorm = lower (tNorm (FullNorm id id) (FullNorm id id)) $ raise (tNorm (FullNorm id id) (FullNorm id id)) $ oC where
  oC :: C 2 ⊗ C 4
  oC = Tensor (konst 1)

exampleCoerce :: DualVector (C 2) ⊗ DualVector (C 4)
exampleCoerce = coerce $ exampleTNorm where
  x ::  C 2 +> (DualVector (C 4))
  x = LinearMap (konst 1)


exampleArr :: DualVector (C 2 ⊗ C 2)
exampleArr = bar $ baz where 
  foo :: DualVector (C 2) +> DualVector (C 2 ⊗ C 2)
  foo = LinearMap (konst 1)
  bar = arr foo :: DualVector (C 2) -+> DualVector (C 2 ⊗ C 2)
  baz :: C 2
  baz = konst 1

-- exampleFoo ::  (C 2 ⊗ C 2) +> (C 2 )
exampleFoo = f where
  f = LinearMap (fromList [1,2,3,4,5,6,7,8]) :: (C 2 ⊗ C 2) +> (C 2 )
  tensor = getAntilinearFunction vectorConjugate $ transposeTensor $ coerce f :: DualVector (DualVector (C 2)) ⊗ DualVector (C 2 ⊗ C 2)
  lm = coerce tensor :: DualVector (C 2) +> DualVector (C 2 ⊗ C 2)

-- | Print the concrete inner product (for REPL / smoke scripts).
-- exampleMPSInnerDemo :: IO ()
-- exampleMPSInnerDemo = diagnoseExampleMPSInnerC22 >> putStrLn ("⟨ψ|ψ⟩ = " ++ show exampleMPSInnerC22)

-- | Step through 'exampleMPSC22' / 'mpsInner' and report where evaluation fails.
-- diagnoseExampleMPSInnerC22 :: IO ()
-- diagnoseExampleMPSInnerC22 =
--   withMPS3 exampleMPSC22 $ \l b r -> do
--     putStrLn "=== Fixed3General mpsInner @C2 diagnostic ==="
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
