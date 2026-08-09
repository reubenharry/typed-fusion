{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{- HLINT ignore "Redundant $" -}

-- | Three-site MPS with abstract @LinearSpace@ operands and heterogeneous
-- boundary sites. Open boundaries use @Scalar bond@ as the unit object.
--
-- 'siteDagger' flattens the tensor domain via 'fuseBond' then uses 'dagger'
-- on the self-dual @C (n·m)@ (see 'TensorNetwork.Dagger'). Do /not/ dagger
-- through 'tensorNorm': @DualVector (u ⊗ v) = u +> DualVector v@, so the
-- @coerce@ into @Dual u ⊗ Dual v@ makes 'dagger' transpose a nested 'LinearMap'.
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
  , LinearFunction, pattern LinearFunction, DimensionAware (..), LSpace, adjoint, Norm (..), type (-+>), getAntilinearFunction, lfun, SemilinearFunction (SemilinearFunction), VectorSpace (..), Num' , FiniteDimensional )
import Math.LinearMap.Category.Class (asTensor, fromTensor)
import Math.LinearMap.Coercion (curryLinearMap, uncurryLinearMap, (-+$=>))
import Numeric.LinearAlgebra.Static
  ( Sized (konst, create, extract, fromList)
  , C, M, R, Domain (diagR), complex, mul
  )
import Math.LinearMap.Category.Instances ()
import Math.OrphanInstances ()
import Control.Category.Constrained (id)
import GHC.TypeLits (KnownNat, type (*), type (<=), type (-), type (+))
import Numeric.LinearAlgebra.Static.COrphans ()
import Math.LinearMap.Category.Backend.HMatrix ()
import TensorNetwork.MPS.LinmapStorage
import TensorNetwork.Categorical
  ( (⊗^), swapMap, lassocMap, rassocMap, fuseBond, splitBond
   )
import Data.Coerce (coerce)
import qualified Debug.Trace as Debug
import Math.LinearMap.Asserted (flipBilin)
import GHC.TypeNats (natVal)
import Data.Data (Proxy(..))
import GHC.TypeLits (Nat)
import Linear.V (V (..))
import Control.Lens ((&), (.~), (^.), Ixed (ix), (^?), _1, _2, makeLenses)
import Data.Maybe (fromMaybe)
import Data.Foldable (Foldable(toList), foldl')
import qualified Data.Vector as Vector
import qualified Numeric.LinearAlgebra as HM
import Data.VectorSpace.Free (FinSuppSeq(..))
import Data.VectorSpace.Free.FiniteSupportedSequence
import qualified Data.Vector.Unboxed as U
import Data.Finite (Finite, packFinite, getFinite)
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

-- | Orthogonality-center location on an open-boundary 'MPS' of bulk length @n@.
--
-- 'CenterBulk' carries a 'Finite' index into '_mpsBulk', so out-of-range bulk
-- positions are unrepresentable. For @n = 0@ that constructor is uninhabited
-- (left ↔ right only).
data CenterPos (n :: Nat) where
  CenterLeft  :: CenterPos n
  CenterBulk  :: Finite n -> CenterPos n
  CenterRight :: CenterPos n

deriving instance Eq (CenterPos n)
deriving instance Show (CenterPos n)

-- | Open-boundary three-site MPS (@left + bulk + right@).
data MPS (bond :: Type) (phys :: Type) (n :: Nat) = MPS
  { _mpsLeft :: phys +> bond
  , _mpsBulk :: V n ((bond ⊗ phys) +> bond)
  , _mpsRight :: bond +> phys
  }

-- | Matrix-product operator with possibly distinct physical legs.
--
-- Transfer orientation: domain phys = result\/bra (@physOut@), codomain phys =
-- ket (@physIn@). Parameter order puts Category object slots last so
-- @MPO bond n :: Type -> Type -> Type@.
data MPO (bond :: Type) (n :: Nat) (physIn :: Type) (physOut :: Type) = MPO
  { _mpoLeft :: physOut +> (bond ⊗ physIn)
  , _mpoBulk :: V n ((bond ⊗ physOut) +> (bond ⊗ physIn))
  , _mpoRight :: (bond ⊗ physIn) +> physOut
  , _mpoBondDimHint :: Int
  }

makeLenses ''MPS
makeLenses ''MPO

-- | Homogeneous (endomorphism) MPO.

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

-- | Bra pullback for a bulk-shaped map @(u ⊗ v) +> w@.
--
-- For @C n@ the instance flattens via 'fuseBond' (self-dual domain) — see
-- 'siteDaggerC'. Do not dagger through 'tensorNorm' on a tensor domain:
-- @DualVector (u ⊗ v) = u +> DualVector v@, and the nested-'LinearMap'
-- transpose breaks @dagger(f ∘ (g ⊗ id)) = (g† ⊗ id) ∘ dagger f@.
class SiteDagger u v w where
  siteDagger
    :: FullNorm w -> FullNorm v -> FullNorm u
    -> ((u ⊗ v) +> w) -> (w +> (u ⊗ v))

-- | @C n@ instance: @siteDagger f = splitBond ∘ dagger (f ∘ splitBond)@.
instance
  ( KnownNat n, KnownNat m, KnownNat p, KnownNat (n * m)
  ) => SiteDagger (C n) (C m) (C p) where
  siteDagger nw _nv _nu f =
    splitBond @n @m . dagger nw flat (f . splitBond @n @m)
    where
      flat = hermitianNorm :: FullNorm (C (n * m))

-- | Product Riesz map via @coerce :: Dual u ⊗ Dual v ↔ Dual(u ⊗ v)@.
--
-- WARNING: @DualVector (u ⊗ v) = u +> DualVector v@, not @Dual u ⊗ Dual v@.
-- Prefer 'siteDagger' (flatten) for bulk bra pullback; this remains for
-- diagnostics and non-@C@ experiments that do not go through transfer.
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
  postCompose (mps ^. mpsRight)
  . bulkToMap (mps ^. mpsBulk . _1)
  .  (mps ^. mpsLeft)
  . arr lw
  )

-- | ((w ⊗ p') ⊗ p) → ((w ⊗ p) ⊗ p'): swap the two physical legs past each
-- other while leaving the bond fixed (used between left/bulk and bulk/right).
rearrangeBondPhys
  :: forall bond phys. MPSConstraints bond phys =>
  ((bond ⊗ phys) ⊗ phys) +> ((bond ⊗ phys) ⊗ phys)
rearrangeBondPhys =
  lassocMap
    . (Cat.id ⊗^ swapMap)
    . rassocMap

-- | ((w ⊗ p₂') ⊗ p₁') ⊗ p₃ → (w ⊗ p₃) ⊗ (p₁' ⊗ p₂')
prepMPORight
  :: forall bond phys. MPSConstraints bond phys =>
  (((bond ⊗ phys) ⊗ phys) ⊗ phys) +> ((bond ⊗ phys) ⊗ (phys ⊗ phys))
prepMPORight =
  (Cat.id ⊗^ swapMap)
    . lassocMap
    . (Cat.id ⊗^ swapMap)
    . rassocMap
    . (rassocMap ⊗^ Cat.id)

-- | p₃' ⊗ (p₁' ⊗ p₂') → p₁' ⊗ (p₂' ⊗ p₃')
reorderPhysical3
  :: forall phys.
  (LSpace phys, Scalar phys ~ Complex Double) =>
  (phys ⊗ (phys ⊗ phys)) +> (phys ⊗ (phys ⊗ phys))
reorderPhysical3 =
  (Cat.id ⊗^ swapMap)
    . rassocMap
    . (swapMap ⊗^ Cat.id)
    . lassocMap

-- | Flatten a three-site endomorphism MPO to a physical map on @OTimes 3 phys@.
-- Pure morphism wiring (no Riesz / basis sums).
toPhysicalMPO
  :: forall bond phys. MPSConstraints bond phys =>
  MPO bond 1 phys phys -> OTimes 3 phys +> OTimes 3 phys
toPhysicalMPO (MPO l bulk r _) =
  reorderPhysical3
    . (r ⊗^ Cat.id)
    . prepMPORight
    . ((bulk ^. _1 ⊗^ Cat.id) ⊗^ Cat.id)
    . (rearrangeBondPhys ⊗^ Cat.id)
    . lassocMap
    . (l ⊗^ Cat.id)


-- | @OTimes 3 (C p) → C (p³)@: associate left, then fuse pairwise via 'fuseBond'.
--
--   @C p ⊗ (C p ⊗ C p)  ≅  (C p ⊗ C p) ⊗ C p  ≅  C (p·p) ⊗ C p  ≅  C ((p·p)·p)@
physical3ToFlat
  :: forall p.
  (KnownNat p, KnownNat (p * p), KnownNat (p * p * p)) =>
  OTimes 3 (C p) +> C (p * p * p)
physical3ToFlat =
  fuseBond @(p * p) @p
    . (fuseBond @p @p ⊗^ Cat.id)
    . lassocMap

-- | Inverse of 'physical3ToFlat': @C (p³) → OTimes 3 (C p)@.
physical3FromFlat
  :: forall p.
  (KnownNat p, KnownNat (p * p), KnownNat (p * p * p)) =>
  C (p * p * p) +> OTimes 3 (C p)
physical3FromFlat =
  rassocMap
    . (splitBond @p @p ⊗^ Cat.id)
    . splitBond @(p * p) @p

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
  :: forall bond phys. (MPSConstraints bond phys, SiteDagger bond phys bond) =>
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
  (MPSConstraints bond phys, SiteDagger bond phys bond) =>
  FullNorm bond -> FullNorm phys -> MPS bond phys n -> MPS bond phys n -> Scalar bond
mpsInner nb np (MPS lB bB rB) (MPS lK bK rK) =
  transferRightSite nb np rB rK $
    foldl' (\e t -> t e) (transferLeftSite nb np lB lK) transfers
  where
    transfers = uncurry (transferBulkSite nb np) <$> zip (toList bB) (toList bK)

-- | Left-to-right ⟨ψ|H|φ⟩ environment: bra bond ↦ MPO bond ⊗ ket bond.

-- | MPO-column wiring: route the physical leg on the right of
-- a @(mpoBond ⊗ ketBond) ⊗ physOut@ through the MPO site then the ket site.
--
--   @((w ⊗ k) ⊗ physOut)  +>  (w ⊗ k)@
opWire
  :: forall bond physIn physOut.
  (MPSConstraints bond physIn, MPSConstraints bond physOut) =>
  ((bond ⊗ physOut) +> (bond ⊗ physIn))
  -> ((bond ⊗ physIn) +> bond)
  -> (((bond ⊗ bond) ⊗ physOut) +> (bond ⊗ bond))
opWire op ket =
  (Cat.id ⊗^ ket)
    . (Cat.id ⊗^ swapMap)
    . rassocMap
    . (op ⊗^ Cat.id)
    . lassocMap
    . (Cat.id ⊗^ swapMap)
    . rassocMap

-- | MPO–MPO bulk wiring: @op1@ (outer, @b → c@) then @op2@ (inner, @a → b@);
-- product bond stays @w₁ ⊗ w₂@.
--
--   @((w₁ ⊗ w₂) ⊗ c)  +>  ((w₁ ⊗ w₂) ⊗ a)@
composeOpWire
  :: forall bond a b c.
  (MPSConstraints bond a, MPSConstraints bond b, MPSConstraints bond c) =>
  ((bond ⊗ c) +> (bond ⊗ b))
  -> ((bond ⊗ b) +> (bond ⊗ a))
  -> (((bond ⊗ bond) ⊗ c) +> ((bond ⊗ bond) ⊗ a))
composeOpWire op1 op2 =
  lassocMap
    . (Cat.id ⊗^ op2)
    . (Cat.id ⊗^ swapMap)
    . rassocMap
    . (op1 ⊗^ Cat.id)
    . lassocMap
    . (Cat.id ⊗^ swapMap)
    . rassocMap

-- | Left boundary ⟨bra|op|ket⟩ transfer: no incoming environment.
transferMPOLeftSite
  :: forall bond physIn physOut.
  (MPSConstraints bond physIn, MPSConstraints bond physOut) =>
  FullNorm bond -> FullNorm physOut ->
  LeftSite bond physOut
  -> (physOut +> (bond ⊗ physIn))
  -> LeftSite bond physIn
  -> (bond +> (bond ⊗ bond))
transferMPOLeftSite nb npOut bra op ket =
  (Cat.id ⊗^ ket) . op . dagger nb npOut bra

-- | Bulk ⟨bra|op|ket⟩ transfer update.
transferMPOBulkSite
  :: forall bond physIn physOut.
  (MPSConstraints bond physIn, MPSConstraints bond physOut, SiteDagger bond physOut bond) =>
  FullNorm bond -> FullNorm physOut ->
  BulkSite bond physOut
  -> ((bond ⊗ physOut) +> (bond ⊗ physIn))
  -> BulkSite bond physIn
  -> (bond +> (bond ⊗ bond))
  -> (bond +> (bond ⊗ bond))
transferMPOBulkSite nb npOut bra op ket env =
  opWire op ket . (env ⊗^ Cat.id) . siteDagger nb npOut nb bra

-- | Right boundary close: dagger the bra, apply op after the ket physical
-- leg, then trace.
transferMPORightSite
  :: forall bond physIn physOut.
  (MPSConstraints bond physIn, MPSConstraints bond physOut) =>
  FullNorm bond -> FullNorm physOut ->
  RightSite bond physOut
  -> ((bond ⊗ physIn) +> physOut)
  -> RightSite bond physIn
  -> (bond +> (bond ⊗ bond))
  -> Scalar bond
transferMPORightSite nb npOut bra op ket env =
  trace $ dagger npOut nb bra . op . (Cat.id ⊗^ ket) . env

-- | ⟨ψ|H|φ⟩ via left-to-right MPO–MPS transfer: bra on @physOut@, ket on @physIn@.
mpsMPOInner
  :: forall bond physIn physOut (n :: Nat).
  (MPSConstraints bond physIn, MPSConstraints bond physOut, SiteDagger bond physOut bond) =>
  FullNorm bond -> FullNorm physOut ->
  MPS bond physOut n -> MPO bond n physIn physOut -> MPS bond physIn n -> Scalar bond
mpsMPOInner nb npOut (MPS lB bB rB) (MPO lO bO rO _) (MPS lK bK rK) =
  transferMPORightSite nb npOut rB rO rK $
    foldl' (\e t -> t e) (transferMPOLeftSite nb npOut lB lO lK) transfers
  where
    transfers =
      (\(bra, op, ket) -> transferMPOBulkSite nb npOut bra op ket)
        <$> zip3 (toList bB) (toList bO) (toList bK)

--------------------------------------------------------------------------------
-- Effective Hamiltonian (morphism apply; no basis enumeration)
--------------------------------------------------------------------------------

-- | Left MPO environment: @bond +> (bond ⊗ bond)@.
type LeftMPOEnv bond = bond +> (bond ⊗ bond)

-- | Right MPO environment: @(bond ⊗ bond) +> bond@.
type RightMPOEnv bond = (bond ⊗ bond) +> bond

-- | Left environment through the left boundary site.
leftMPOEnv
  :: forall bond physIn physOut.
  (MPSConstraints bond physIn, MPSConstraints bond physOut) =>
  FullNorm bond -> FullNorm physOut ->
  LeftSite bond physOut -> (physOut +> (bond ⊗ physIn)) -> LeftSite bond physIn ->
  LeftMPOEnv bond
leftMPOEnv = transferMPOLeftSite

-- | Right environment through the right boundary site (no trace).
rightMPOEnv
  :: forall bond physIn physOut.
  (MPSConstraints bond physIn, MPSConstraints bond physOut) =>
  FullNorm bond -> FullNorm physOut ->
  RightSite bond physOut -> ((bond ⊗ physIn) +> physOut) -> RightSite bond physIn ->
  RightMPOEnv bond
rightMPOEnv nb npOut bra op ket =
  dagger npOut nb bra . op . (Cat.id ⊗^ ket)

-- | Bulk-centre apply: @Heff x = R ∘ opWire op x ∘ (L ⊗^ id_phys)@.
effectiveHBulk
  :: forall bond physIn physOut.
  (MPSConstraints bond physIn, MPSConstraints bond physOut) =>
  LeftMPOEnv bond ->
  ((bond ⊗ physOut) +> (bond ⊗ physIn)) ->
  RightMPOEnv bond ->
  BulkSite bond physIn ->
  BulkSite bond physOut
effectiveHBulk leftEnv op rightEnv centreKet =
  rightEnv . opWire op centreKet . (leftEnv ⊗^ Cat.id)

-- | Left-centre apply: @Heff x = R ∘ (id ⊗^ x) ∘ op@.
effectiveHLeft
  :: forall bond physIn physOut.
  (MPSConstraints bond physIn, MPSConstraints bond physOut) =>
  (physOut +> (bond ⊗ physIn)) ->
  RightMPOEnv bond ->
  LeftSite bond physIn ->
  LeftSite bond physOut
effectiveHLeft op rightEnv centreKet =
  rightEnv . (Cat.id ⊗^ centreKet) . op

-- | Right-centre apply: @Heff x = op ∘ (id ⊗^ x) ∘ L@.
effectiveHRight
  :: forall bond physIn physOut.
  (MPSConstraints bond physIn, MPSConstraints bond physOut) =>
  LeftMPOEnv bond ->
  ((bond ⊗ physIn) +> physOut) ->
  RightSite bond physIn ->
  RightSite bond physOut
effectiveHRight leftEnv op centreKet =
  op . (Cat.id ⊗^ centreKet) . leftEnv

-- | Replace the bulk site of a three-site (@n = 1@ bulk) MPS.
mpsWithBulkSite
  :: BulkSite bond phys -> MPS bond phys 1 -> MPS bond phys 1
mpsWithBulkSite site mps =
  mps & mpsBulk . _1 .~ site

-- | Environments and bulk @Heff@ on a three-site (@bulk length 1@) endomorphism chain.
effectiveHBulk3
  :: forall bond phys.
  MPSConstraints bond phys =>
  FullNorm bond -> FullNorm phys ->
  MPS bond phys 1 -> MPO bond 1 phys phys ->
  BulkSite bond phys -> BulkSite bond phys
effectiveHBulk3 nb np mps mpo = effectiveHBulk
    (leftMPOEnv nb np (mps ^. mpsLeft) (mpo ^. mpoLeft) (mps ^. mpsLeft))
    (mpo ^. mpoBulk . _1)
    (rightMPOEnv nb np (mps ^. mpsRight) (mpo ^. mpoRight) (mps ^. mpsRight))

-- | Network bilinear form at the bulk centre: close @R ∘ opWire ∘ (L ⊗ id) ∘ siteDagger@
-- via 'transferMPORightSite' (same contraction as 'mpsMPOInner').
-- Hilbert–Schmidt @braCentre <.> Heff ketCentre@ is /not/ this pairing unless the
-- mixed-canonical metric identifies them.
effectiveHBulkInner
  :: forall bond phys.
  (MPSConstraints bond phys, SiteDagger bond phys bond) =>
  FullNorm bond -> FullNorm phys ->
  MPS bond phys 1 -> MPO bond 1 phys phys ->
  BulkSite bond phys -> BulkSite bond phys -> Scalar bond
effectiveHBulkInner nb np mps mpo braCentre ketCentre =
  let l = leftMPOEnv nb np (mps ^. mpsLeft) (mpo ^. mpoLeft) (mps ^. mpsLeft)
      op = mpo ^. mpoBulk . _1
      env =
        opWire op ketCentre
          . (l ⊗^ Cat.id)
          . siteDagger nb np nb braCentre
  in transferMPORightSite nb np (mps ^. mpsRight) (mpo ^. mpoRight) (mps ^. mpsRight) env

--------------------------------------------------------------------------------
-- MPO × MPS (exact product bond, then SVD truncate to fixed χ)
--------------------------------------------------------------------------------

-- | Apply an MPO to an MPS sitewise. The product bond stays in tensor form
-- @bond ⊗ bond@ (no truncation). Result physical space is @physOut@.
mpoApplyExact
  :: forall bond physIn physOut (n :: Nat).
  (MPSConstraints bond physIn, MPSConstraints bond physOut) =>
  MPO bond n physIn physOut -> MPS bond physIn n -> MPS (bond ⊗ bond) physOut n
mpoApplyExact (MPO lO bO rO _) (MPS lK bK rK) =
  MPS
    ((Cat.id ⊗^ lK) . lO)
    (V . Vector.fromList $ zipWith opWire (toList bO) (toList bK))
    (rO . (Cat.id ⊗^ rK))

-- | Compose two MPOs sitewise (@h₁ ∘ h₂@ = Category @h1 . h2@). Product bond
-- stays @bond ⊗ bond@ (no truncation).
mpoComposeExact
  :: forall bond a b c (n :: Nat).
  (MPSConstraints bond a, MPSConstraints bond b, MPSConstraints bond c) =>
  MPO bond n b c -> MPO bond n a b -> MPO (bond ⊗ bond) n a c
mpoComposeExact (MPO l1 b1 r1 d1) (MPO l2 b2 r2 d2) =
  MPO
    (lassocMap . (Cat.id ⊗^ l2) . l1)
    (V . Vector.fromList $ zipWith composeOpWire (toList b1) (toList b2))
    (r1 . (Cat.id ⊗^ r2) . rassocMap)
    (d1 * d2)

-- | Fuse a Kronecker product bond @C a ⊗ C b@ into @C (a·b)@ on every site.
fuseMPSBond
  :: forall a b p (n :: Nat).
  ( KnownNat a, KnownNat b, KnownNat p, KnownNat (a * b)
  , KnownNat ((a * b) * p), KnownNat (p * (a * b))
  , MPSConstraints (C a ⊗ C b) (C p)
  , MPSConstraints (C (a * b)) (C p)
  ) =>
  MPS (C a ⊗ C b) (C p) n -> MPS (C (a * b)) (C p) n
fuseMPSBond (MPS l bulk r) =
  MPS
    (fuseBond @a @b . l)
    ((\s -> fuseBond @a @b . s . (splitBond @a @b ⊗^ Cat.id)) <$> bulk)
    (r . splitBond @a @b)

createOrFail :: Sized t s d => d t -> s
createOrFail = fromMaybe (error "createOrFail: size mismatch") . create

-- | Pad or truncate matrix columns to width @n@.
fitColsHM :: Int -> HM.Matrix (Complex Double) -> HM.Matrix (Complex Double)
fitColsHM n m
  | HM.cols m >= n = HM.subMatrix (0, 0) (HM.rows m, n) m
  | otherwise      = m HM.||| HM.konst 0 (HM.rows m, n - HM.cols m)

-- | Pad or truncate matrix rows to height @n@.
fitRowsHM :: Int -> HM.Matrix (Complex Double) -> HM.Matrix (Complex Double)
fitRowsHM n m
  | HM.rows m >= n = HM.subMatrix (0, 0) (n, HM.cols m) m
  | otherwise      = HM.konst 0 (n - HM.rows m, HM.cols m) HM.=== m

fitSingularBondFromHM :: forall b. KnownNat b => HM.Vector Double -> R b
fitSingularBondFromHM s =
  createOrFail $
    let b = fromIntegral (natVal (Proxy @b))
        xs = HM.toList s
    in HM.fromList $
         if length xs >= b then take b xs else xs ++ replicate (b - length xs) 0

-- | Thin SVD with bond truncation/padding to a typed width @b@.
--
-- Returns @U@ (@M m b@), singular values (@R b@), and @Vᵀ@ (@M b n@) with
-- @M ≈ U · diag s · Vᵀ@. Dynamic 'extract' only at the LAPACK boundary.
svdCut
  :: forall m n b. (KnownNat m, KnownNat n, KnownNat b)
  => M m n -> (M m b, R b, M b n)
svdCut mat =
  let b = fromIntegral (natVal (Proxy @b))
      (u, s, v) = HM.thinSVD (extract mat)
  in ( createOrFail (fitColsHM b u)
     , fitSingularBondFromHM @b s
     , createOrFail (fitRowsHM b (HM.tr v))
     )

-- | Factor @C dom +> C cod@ as @(C dom +> C χ) ; (C χ +> C cod)@, keeping the
-- leading @χ@ singular values (pad with zeros if rank is smaller).
--
-- Puts @Σ@ in the /left/ factor: @(Σ·V†, U)@. Prefer 'svdSplitLeftCanonical'
-- when the left factor must be left-canonical (coisometry @V†@).
svdSplit
  :: forall dom cod χ.
  (KnownNat dom, KnownNat cod, KnownNat χ) =>
  C dom +> C cod -> (C dom +> C χ, C χ +> C cod)
svdSplit (LinearMap lm) =
  let (u, s, vt) = svdCut @cod @dom @χ lm
  in ( LinearMap (mul (diagR 0 (complex s)) vt)
     , LinearMap u
     )

-- | Left-looking TT-SVD / left-canonical gauge split: @(V†, U·Σ)@.
--
-- For a flatten @C (χ·p) +> C χ'@ with matrix layout @χ' × (χ·p)@, @V†@ is a
-- coisometry (@V† ∘ (V†)† = id@ on the kept bond), so the reconstructed bulk
-- site is left-canonical. Singular weight sits in the right factor.
svdSplitLeftCanonical
  :: forall dom cod χ.
  (KnownNat dom, KnownNat cod, KnownNat χ) =>
  C dom +> C cod -> (C dom +> C χ, C χ +> C cod)
svdSplitLeftCanonical (LinearMap lm) =
  let (u, s, vt) = svdCut @cod @dom @χ lm
  in ( LinearMap vt
     , LinearMap (u `mul` diagR 0 (complex s))
     )

-- | Polar-decompose a left boundary site @A = m ∘ iso@ with @iso = U·V†@ an
-- isometry (@iso† ∘ iso = id@ on @C p@, requires @χ ≥ p@) and @m = U·Σ·U†@.
-- Returned as @(m, iso)@. LAPACK boundary only (like 'svdSplit').
polarLeftSite
  :: forall p χ. (KnownNat p, KnownNat χ)
  => C p +> C χ -> (C χ +> C χ, C p +> C χ)
polarLeftSite (LinearMap a) =
  let (u, s, vt) = svdCut @χ @p @p a
  in ( LinearMap (u `mul` diagR 0 (complex s) `mul` HM.tr u)
     , LinearMap (u `mul` vt)
     )

-- | Polar-decompose a right boundary site @B = iso ∘ m@ with @iso = U·V†@ a
-- coisometry (@iso ∘ iso† = id@ on @C p@, requires @χ ≥ p@) and @m = V·Σ·V†@.
-- Returned as @(iso, m)@.
polarRightSite
  :: forall χ p. (KnownNat χ, KnownNat p)
  => C χ +> C p -> (C χ +> C p, C χ +> C χ)
polarRightSite (LinearMap b) =
  let (u, s, vt) = svdCut @p @χ @p b
  in ( LinearMap (u `mul` vt)
     , LinearMap (HM.tr vt `mul` diagR 0 (complex s) `mul` vt)
     )

-- | Mixed-canonical gauge about the bulk centre of a three-site MPS: the left
-- boundary becomes an isometry, the right boundary a coisometry, and both
-- polar factors are absorbed into the centre. The represented physical tensor
-- is unchanged ('toPhysicalMPS' invariant).
mixedCanonicalCentre3
  :: forall χ p.
  (KnownNat χ, KnownNat p, MPSConstraints (C χ) (C p)) =>
  MPS (C χ) (C p) 1 -> MPS (C χ) (C p) 1
mixedCanonicalCentre3 (MPS l bulk r) =
  let (mL, lIso) = polarLeftSite l
      (rIso, mR) = polarRightSite r
      centre = mR . (bulk ^. _1) . (mL ⊗^ Cat.id)
  in MPS lIso (bulk & _1 .~ centre) rIso

-- | Flatten @(bond ⊗ physical)@ for a left-looking SVD cut.
siteForLeftSVD
  :: forall bl p br.
  ( KnownNat bl, KnownNat p, KnownNat br
  , KnownNat (p * bl), KnownNat (bl * p)
  , p * bl ~ bl * p
  ) =>
  (C bl ⊗ C p) +> C br -> C (bl * p) +> C br
siteForLeftSVD f = f . swapMap . splitBond @p @bl

-- | Inverse of 'siteForLeftSVD'.
siteFromLeftSVD
  :: forall bl p br.
  ( KnownNat bl, KnownNat p, KnownNat br
  , KnownNat (p * bl), KnownNat (bl * p)
  , p * bl ~ bl * p
  ) =>
  C (bl * p) +> C br -> (C bl ⊗ C p) +> C br
siteFromLeftSVD g = g . fuseBond @p @bl . swapMap

-- | Right-looking flatten: curry the left bond, then fuse @(p +> br)@ to @C (p·br)@.
-- Matches the nested @getLinearMap@ layout used by the old 'normalizeRight'.
siteForRightSVD
  :: forall bl p br.
  ( KnownNat bl, KnownNat p, KnownNat br, KnownNat (p * br) ) =>
  (C bl ⊗ C p) +> C br -> C bl +> C (p * br)
siteForRightSVD f =
  let curried = curryLinearMap -+$=> f :: C bl +> (C p +> C br)
  in arr (LinearFunction $ \x ->
        fuseBond @p @br $ (asTensor -+$=> (curried $ x :: C p +> C br)))

-- | Inverse of 'siteForRightSVD'.
siteFromRightSVD
  :: forall bl p br.
  ( KnownNat bl, KnownNat p, KnownNat br, KnownNat (p * br) ) =>
  C bl +> C (p * br) -> (C bl ⊗ C p) +> C br
siteFromRightSVD g =
  uncurryLinearMap -+$=>
    (arr (LinearFunction $ \x ->
       fromTensor -+$=> (splitBond @p @br $ (g $ x)) :: C p +> C br))

--------------------------------------------------------------------------------
-- One-site gauge transport (fixed uniform χ)
--------------------------------------------------------------------------------

type GaugeShiftNats χ p =
  ( KnownNat χ, KnownNat p
  , KnownNat (χ * p), KnownNat (p * χ)
  , χ * p ~ p * χ
  , p <= χ
  )

-- | Left-canonicalize a bulk site: @(V†, U·Σ)@ with residual on the right bond.
leftCanonicalizeBulk
  :: forall χ p.
  GaugeShiftNats χ p =>
  BulkSite (C χ) (C p) -> (BulkSite (C χ) (C p), C χ +> C χ)
leftCanonicalizeBulk b =
  let flat = siteForLeftSVD @χ @p @χ b
      (vt, g) = svdSplitLeftCanonical @(χ * p) @χ @χ flat
  in (siteFromLeftSVD @χ @p @χ vt, g)

-- | Right-canonicalize a bulk site: @(Σ·V†, U-layout)@ with residual on the left bond.
rightCanonicalizeBulk
  :: forall χ p.
  GaugeShiftNats χ p =>
  BulkSite (C χ) (C p) -> (C χ +> C χ, BulkSite (C χ) (C p))
rightCanonicalizeBulk b =
  let flat = siteForRightSVD @χ @p @χ b
      (g, v) = svdSplit @χ @(p * χ) @χ flat
  in (g, siteFromRightSVD @χ @p @χ v)

setBulk
  :: forall n a. KnownNat n
  => Finite n -> a -> V n a -> V n a
setBulk j x (V v) =
  let i = fromIntegral (getFinite j)
  in case v ^? ix i of
    Nothing -> error ("setBulk: bad index " ++ show i)
    Just _ -> V (v & ix i .~ x)

getBulkAt
  :: forall n a. KnownNat n
  => Finite n -> V n a -> a
getBulkAt j (V v) =
  let i = fromIntegral (getFinite j)
  in fromMaybe (error ("getBulkAt: bad index " ++ show i)) (v ^? ix i)

-- | First bulk index, when @n >= 1@.
bulkFirst :: forall n. KnownNat n => Maybe (Finite n)
bulkFirst = packFinite 0

-- | Successor bulk index, or 'Nothing' if @j@ is already last.
bulkSucc :: forall n. KnownNat n => Finite n -> Maybe (Finite n)
bulkSucc j = packFinite (getFinite j + 1)

-- | Predecessor bulk index, or 'Nothing' if @j@ is already first.
bulkPred :: forall n. KnownNat n => Finite n -> Maybe (Finite n)
bulkPred j =
  let i = getFinite j
  in if i == 0 then Nothing else packFinite (i - 1)

-- | Last bulk index, when @n >= 1@.
bulkLast :: forall n. KnownNat n => Maybe (Finite n)
bulkLast =
  let n = natVal (Proxy @n)
  in if n == 0 then Nothing else packFinite (toInteger n - 1)

-- | Move the orthogonality center one site to the right.
--
-- Precondition: @mps@ is mixed-canonical about @pos@. Leaves a left-canonical
-- site behind and absorbs the residual into the next site. Bond type stays @C χ@.
shiftGaugeRight
  :: forall χ p (n :: Nat).
  (GaugeShiftNats χ p, KnownNat n, MPSConstraints (C χ) (C p)) =>
  CenterPos n -> MPS (C χ) (C p) n -> (CenterPos n, MPS (C χ) (C p) n)
shiftGaugeRight pos (MPS l bulk r) =
  case pos of
    CenterRight ->
      error "shiftGaugeRight: already at right boundary"
    CenterLeft ->
      case bulkFirst @n of
        Nothing ->
          let (m, lIso) = polarLeftSite @p @χ l
          in (CenterRight, MPS lIso bulk (r . m))
        Just j0 ->
          let (m, lIso) = polarLeftSite @p @χ l
              b0 = getBulkAt j0 bulk
              b0' = b0 . (m ⊗^ Cat.id)
          in (CenterBulk j0, MPS lIso (setBulk j0 b0' bulk) r)
    CenterBulk j ->
      let b = getBulkAt j bulk
          (bLC, g) = leftCanonicalizeBulk @χ @p b
          bulkLC = setBulk j bLC bulk
      in case bulkSucc j of
           Nothing ->
             (CenterRight, MPS l bulkLC (r . g))
           Just j' ->
             let bNext = getBulkAt j' bulkLC
                 bNext' = bNext . (g ⊗^ Cat.id)
             in (CenterBulk j', MPS l (setBulk j' bNext' bulkLC) r)

-- | Move the orthogonality center one site to the left.
--
-- Precondition: @mps@ is mixed-canonical about @pos@. Leaves a right-canonical
-- site behind and absorbs the residual into the previous site. Bond type stays @C χ@.
shiftGaugeLeft
  :: forall χ p (n :: Nat).
  (GaugeShiftNats χ p, KnownNat n, MPSConstraints (C χ) (C p)) =>
  CenterPos n -> MPS (C χ) (C p) n -> (CenterPos n, MPS (C χ) (C p) n)
shiftGaugeLeft pos (MPS l bulk r) =
  case pos of
    CenterLeft ->
      error "shiftGaugeLeft: already at left boundary"
    CenterRight ->
      case bulkLast @n of
        Nothing ->
          let (rIso, m) = polarRightSite @χ @p r
          in (CenterLeft, MPS (m . l) bulk rIso)
        Just jLast ->
          let (rIso, m) = polarRightSite @χ @p r
              bLast = getBulkAt jLast bulk
              bLast' = m . bLast
          in (CenterBulk jLast, MPS l (setBulk jLast bLast' bulk) rIso)
    CenterBulk j ->
      let b = getBulkAt j bulk
          (g, bRC) = rightCanonicalizeBulk @χ @p b
          bulkRC = setBulk j bRC bulk
      in case bulkPred j of
           Nothing ->
             (CenterLeft, MPS (g . l) bulkRC r)
           Just j' ->
             let bPrev = getBulkAt j' bulkRC
                 bPrev' = g . bPrev
             in (CenterBulk j', MPS l (setBulk j' bPrev' bulkRC) r)

-- | Put the orthogonality center on the left: right-canonicalize every site to
-- the right of the left boundary (walk 'shiftGaugeLeft' from 'CenterRight').
mixedCanonicalLeft
  :: forall χ p (n :: Nat).
  (GaugeShiftNats χ p, KnownNat n, MPSConstraints (C χ) (C p)) =>
  MPS (C χ) (C p) n -> MPS (C χ) (C p) n
mixedCanonicalLeft = walkLeft (fromIntegral (natVal (Proxy @n)) + 1) . shiftGaugeLeft CenterRight
  where
    walkLeft :: Int -> (CenterPos n, MPS (C χ) (C p) n) -> MPS (C χ) (C p) n
    walkLeft _ (CenterLeft, mps) = mps
    walkLeft 0 _ = error "mixedCanonicalLeft: failed to reach left boundary"
    walkLeft k (pos, mps) = walkLeft (k - 1) (shiftGaugeLeft pos mps)

-- | Put the orthogonality center on the right: left-canonicalize every site to
-- the left of the right boundary (walk 'shiftGaugeRight' from 'CenterLeft').
mixedCanonicalRight
  :: forall χ p (n :: Nat).
  (GaugeShiftNats χ p, KnownNat n, MPSConstraints (C χ) (C p)) =>
  MPS (C χ) (C p) n -> MPS (C χ) (C p) n
mixedCanonicalRight = walkRight (fromIntegral (natVal (Proxy @n)) + 1) . shiftGaugeRight CenterLeft
  where
    walkRight :: Int -> (CenterPos n, MPS (C χ) (C p) n) -> MPS (C χ) (C p) n
    walkRight _ (CenterRight, mps) = mps
    walkRight 0 _ = error "mixedCanonicalRight: failed to reach right boundary"
    walkRight k (pos, mps) = walkRight (k - 1) (shiftGaugeRight pos mps)

-- | Three-site specialisation of 'mixedCanonicalLeft'.
mixedCanonicalLeft3
  :: forall χ p.
  (GaugeShiftNats χ p, MPSConstraints (C χ) (C p)) =>
  MPS (C χ) (C p) 1 -> MPS (C χ) (C p) 1
mixedCanonicalLeft3 = mixedCanonicalLeft

-- | Three-site specialisation of 'mixedCanonicalRight'.
mixedCanonicalRight3
  :: forall χ p.
  (GaugeShiftNats χ p, MPSConstraints (C χ) (C p)) =>
  MPS (C χ) (C p) 1 -> MPS (C χ) (C p) 1
mixedCanonicalRight3 = mixedCanonicalRight

-- | Left-to-right TT-SVD: truncate every internal bond from @C big@ to @C χ@.
compressMPS
  :: forall big χ p (n :: Nat).
  ( KnownNat big, KnownNat χ, KnownNat p
  , KnownNat (big * p), KnownNat (p * big)
  , KnownNat (χ * p), KnownNat (p * χ)
  , χ * p ~ p * χ
  ) =>
  MPS (C big) (C p) n -> MPS (C χ) (C p) n
compressMPS (MPS l bulk r) =
  let (l', g0) = svdSplitLeftCanonical @p @big @χ l
      (bulk', gFinal) = go g0 (toList bulk)
  in MPS l' (V (Vector.fromList bulk')) (r . gFinal)
  where
    go
      :: C χ +> C big
      -> [(C big ⊗ C p) +> C big]
      -> ([(C χ ⊗ C p) +> C χ], C χ +> C big)
    go g [] = ([], g)
    go g (s : ss) =
      let absorbed = s . (g ⊗^ Cat.id)
          flat = siteForLeftSVD @χ @p @big absorbed
          (vt, g') = svdSplitLeftCanonical @(χ * p) @big @χ flat
          s' = siteFromLeftSVD @χ @p @χ vt
          (rest, gFinal) = go g' ss
      in (s' : rest, gFinal)

-- | Apply an MPO to an MPS and SVD-truncate the product bond @n·n@ back to @n@.
--
-- Exact site product lives at @C n ⊗ C n@; 'fuseMPSBond' then 'compressMPS'
-- recover a same-type @MPS (C n) (C p)@.
mpoApplyMPS
  :: forall n p (q :: Nat).
  ( KnownNat n, KnownNat p, KnownNat (n * n)
  , KnownNat (n * p), KnownNat (p * n)
  , KnownNat ((n * n) * p), KnownNat (p * (n * n))
  , KnownNat (n * (n * p)), KnownNat ((n * p) * n)
  , n * p ~ p * n
  , MPSConstraints (C n) (C p)
  , MPSConstraints (C n ⊗ C n) (C p)
  , MPSConstraints (C (n * n)) (C p)
  ) =>
  MPO (C n) q (C p) (C p)  -> MPS (C n) (C p) q -> MPS (C n) (C p) q
mpoApplyMPS op psi =
  compressMPS @(n * n) @n @p (fuseMPSBond (mpoApplyExact op psi))

instance (KnownNat n, KnownNat m, KnownNat (m*n), KnownNat (n*m), vb ~ C n, vp ~ C m, KnownNat q) => Show (MPS vb vp q) where show (MPS l b r) = "MPS: Left site is: " ++ show (getLinearMap l) ++ " \nBulk site is: " ++ show (getLinearMap <$>  b) ++ " \nRight site is: " ++ show (getLinearMap r)


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


-- step1 = transferLeftSite (FullNorm id id) (FullNorm id id) (exampleMPSC22 ^. mpsLeft) (exampleMPSC22 ^. mpsLeft) Cat.id
-- step2 = transferBulkSite' (FullNorm id id) (FullNorm id id) (exampleMPSC22 ^. mpsBulk) (exampleMPSC22 ^. mpsBulk) step1


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
