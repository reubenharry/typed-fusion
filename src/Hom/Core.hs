{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Term-level symbolic SU(2): cups, Hom, Mac Lane compose.
--
-- Singletons: 'Hom.Singletons'.
-- 'RepV' / fuse: 'Hom.RepV'.
-- F-moves / fuseMap: 'Hom.FMove'.
-- Concrete spines + smokes: 'Hom.Smoke'.
--
-- Layers: 'Obj' → 'HomUnfused' (Kronecker); 'Obj' → 'HomFused' via
-- 'ObjSpineSU2' / 'ObjRep' with genealogy 'RepV' / 'FuseRep' morphisms;
-- 'HomInter' = trivial sector of fused Hom (same compose via embed/filter).
-- Cups: genealogy 'cup' / 'capUnfusedObj'.
module Hom.Core where

import Data.Complex (Complex ((:+)), conjugate, magnitude, realPart)
import Data.Proxy (Proxy (..))
import Data.Type.Equality ((:~:) (Refl))
import Data.VectorSpace (AdditiveGroup (zeroV, (^-^)), InnerSpace ((<.>)), Scalar, VectorSpace ((*^)))
import GHC.TypeLits (KnownNat, Nat, sameNat, type (+))
import Control.Arrow.Constrained (($), arr)
import Control.Category.Constrained.Prelude (Category (..))
import Categorical.Associative (Associative (..))
import Categorical.Bifunctor (Bifunctor (..), PFunctor (..), QFunctor (..))
import Categorical.Braided (Braided (..))
import Categorical.Monoidal (Monoidal (..))
import Fusion.Obj (Obj)
import qualified Fusion.Obj as FObj
import Hom.Expr
import Hom.FMove
import Hom.RepV
import Hom.Singletons
import Hom.TypeLevel
import Math.LinearMap.Asserted (getLinearFunction)
import Math.LinearMap.Category
  ( DualVector
  , TensorSpace
  , (-+$>)
  , idTensor
  , pattern LinearFunction
  , trace
  , type (+>)
  , type (⊗)
  , (⊗)
  )
import Math.LinearMap.Category.Backend.HMatrix ()
import Math.LinearMap.Category.Instances ()
import Math.LinearMap.Category.Class (LinearSpace, asTensor, fromTensor)
import Math.LinearMap.Coercion ((-+$=>))
import Math.VectorSpace.DimensionAware (toArray, unsafeFromArray)
import Numeric.LinearAlgebra.Static (C, konst)
import qualified Data.Vector.Storable as VS
import Categorical.Linear
  ( lunit
  , lunitInv
  , lassocMap
  , rassocMap
  , runit
  , runitInv
  , swapMap
  , (⊗^)
  )

import Prelude hiding (id, (.), ($))

--------------------------------------------------------------------------------
-- Unit packaging + fused cups
--------------------------------------------------------------------------------

-- | Unit amplitude as @ToVObj ('Atom 0)@ (= @C 1@).
unitToVFromScalar :: Complex Double -> C 1
unitToVFromScalar s = konst s

-- | Read the amplitude from @C 1@ by pairing against @1@.
unitToVScalar :: C 1 -> Complex Double
unitToVScalar u = (konst 1 :: C 1) <.> u

--------------------------------------------------------------------------------
-- Unfused composition (compact closed on Obj / HomUnfused)
--
--   compose f g = unitor ∘ (cup ⊗ id) ∘ assoc ∘ (f ⊗ g)
--
-- Hom elements are Dual-left @Dual(ToVObj a) ⊗ ToVObj b@. Unitors below are
-- shared with the Monoidal instance; Obj cups use 'ToVObj'.
--------------------------------------------------------------------------------

-- | Unfused morphisms @a → b@: Dual-left packing on tree spaces
-- @Dual(ToVObj a) ⊗ ToVObj b@ (@'Tensor@ = Kronecker).
newtype HomUnfused (a :: Obj Nat) (b :: Obj Nat) = HomUnfused
  { unHomUnfused :: DualVector (ToVObj a) ⊗ ToVObj b }

-- | Fused morphisms @a → b@: 'Obj' trees, payload is genealogy 'RepV' of
-- 'FuseRep (ObjRep a) (ObjRep b)' after 'ObjSpineSU2' (SU(2) dual≅primal;
-- left child plays dual). Compose via 'composeHomTrees' on those leaf reps.
newtype HomFused (a :: Obj Nat) (b :: Obj Nat) = HomFused
  { unHomFused :: RepV (FuseRep (ObjRep a) (ObjRep b)) }

-- | Intertwiners @a → b@: trivial total-charge sector of fused Hom
-- (@'FilterTrivial' of 'FuseRep (ObjRep a) (ObjRep b)'@). Compose reuses
-- 'composeHomTrees' via 'embedTrivialRepV' \/ 'filterTrivialRepV'.
newtype HomInter (a :: Obj Nat) (b :: Obj Nat) = HomInter
  { unHomInter :: RepV (FilterTrivial (FuseRep (ObjRep a) (ObjRep b))) }

-- | Left unitor @C 1 ⊗ v → v@ (monoidal unit = @ToVObj (Atom 0)@).
unitLunit
  :: forall v
   . ( LinearSpace v
     , Scalar v ~ Complex Double
     , TensorSpace (C 1 ⊗ v)
     )
  => (C 1 ⊗ v) +> v
unitLunit = lunit

-- | Inverse of 'unitLunit': @v → C 1 ⊗ v@.
unitLcounit
  :: forall v
   . ( LinearSpace v
     , Scalar v ~ Complex Double
     , TensorSpace (C 1 ⊗ v)
     )
  => v +> (C 1 ⊗ v)
unitLcounit = lunitInv

-- | Right unitor @v ⊗ C 1 → v@.
unitRunit
  :: forall v
   . ( LinearSpace v
     , Scalar v ~ Complex Double
     )
  => (v ⊗ C 1) +> v
unitRunit = runit

-- | Inverse of 'unitRunit': @v → v ⊗ C 1@.
unitRcounit
  :: forall v
   . ( LinearSpace v
     , Scalar v ~ Complex Double
     )
  => v +> (v ⊗ C 1)
unitRcounit = runitInv

--------------------------------------------------------------------------------
-- True unfused Hom on Obj trees (ToVObj / Dual-left Hom)
--------------------------------------------------------------------------------

-- | Object spaces for 'HomUnfused': 'ToVObj' is a nested Kronecker / pair space.
class
  ( LinearSpace (ToVObj a)
  , LinearSpace (DualVector (ToVObj a))
  , Scalar (ToVObj a) ~ Complex Double
  , Scalar (DualVector (ToVObj a)) ~ Complex Double
  , TensorSpace (ToVObj a)
  , TensorSpace (DualVector (ToVObj a))
  , TensorSpace ((ToVObj a ⊗ DualVector (ToVObj a)))
  , TensorSpace (ToVObj ('FObj.Atom 0))
  ) =>
  KnownToVObj (a :: Obj Nat)

instance
  ( KnownNat j
  , KnownNat (IrrepDim j)
  ) =>
  KnownToVObj ('FObj.Atom j)

instance (KnownToVObj a, KnownToVObj b) => KnownToVObj ('FObj.Tensor a b)

instance (KnownToVObj a, KnownToVObj b) => KnownToVObj ('FObj.Sum a b)

-- | Unfused evaluation @ε : a ⊗ a* → 𝟙@ on tree spaces.
cupUnfusedObj
  :: forall a
   . KnownToVObj a
  => (ToVObj a ⊗ DualVector (ToVObj a))
  -> ToVObj ('FObj.Atom 0)
cupUnfusedObj t =
  unitToVFromScalar
    ( getLinearFunction
        trace
        (fromTensor -+$=> (swapMap $ t))
    )

-- | Unfused coevaluation @η : 𝟙 → a ⊗ a*@.
capUnfusedObj
  :: forall a
   . KnownToVObj a
  => ToVObj ('FObj.Atom 0)
  -> (ToVObj a ⊗ DualVector (ToVObj a))
capUnfusedObj u = unitToVScalar u *^ idTensor @(ToVObj a)

-- | Identity Hom element on an Obj tree.
idMorObj
  :: forall a
   . KnownToVObj a
  => (DualVector (ToVObj a) ⊗ ToVObj a)
idMorObj = swapMap $ capUnfusedObj @a (unitToVFromScalar 1)

assocComposeObj
  :: forall a b c
   . ( KnownToVObj a
     , KnownToVObj b
     , KnownToVObj c
     )
  => (DualVector (ToVObj a) ⊗ ToVObj b) ⊗ (DualVector (ToVObj b) ⊗ ToVObj c)
  -> DualVector (ToVObj a) ⊗ ((ToVObj b ⊗ DualVector (ToVObj b)) ⊗ ToVObj c)
assocComposeObj t =
  ( (id ⊗^ lassocMap @(ToVObj b) @(DualVector (ToVObj b)) @(ToVObj c))
      . rassocMap
          @(DualVector (ToVObj a))
          @(ToVObj b)
          @(DualVector (ToVObj b) ⊗ ToVObj c)
  )
    $ t

cupTensorIdComposeObj
  :: forall a b c
   . ( KnownToVObj a
     , KnownToVObj b
     , KnownToVObj c
     )
  => DualVector (ToVObj a) ⊗ ((ToVObj b ⊗ DualVector (ToVObj b)) ⊗ ToVObj c)
  -> DualVector (ToVObj a) ⊗ (ToVObj ('FObj.Atom 0) ⊗ ToVObj c)
cupTensorIdComposeObj t =
  (id ⊗^ (arr (LinearFunction (cupUnfusedObj @b)) ⊗^ id)) $ t

unitorComposeObj
  :: forall a c
   . ( KnownToVObj a
     , KnownToVObj c
     )
  => DualVector (ToVObj a) ⊗ (ToVObj ('FObj.Atom 0) ⊗ ToVObj c)
  -> (DualVector (ToVObj a) ⊗ ToVObj c)
unitorComposeObj t =
  (id ⊗^ unitLunit @(ToVObj c)) $ t

-- | Unfused Hom composition: apply Mac Lane ladder once to @f ⊗ g@.
-- @λ ∘ (ε⊗id) ∘ α@.
composeMorObj
  :: forall a b c
   . ( KnownToVObj a
     , KnownToVObj b
     , KnownToVObj c
     , TensorSpace ((DualVector (ToVObj a) ⊗ ToVObj b))
     , TensorSpace ((DualVector (ToVObj b) ⊗ ToVObj c))
     , Scalar ((DualVector (ToVObj a) ⊗ ToVObj b)) ~ Complex Double
     , Scalar ((DualVector (ToVObj b) ⊗ ToVObj c)) ~ Complex Double
     )
  => (DualVector (ToVObj a) ⊗ ToVObj b)
  -> (DualVector (ToVObj b) ⊗ ToVObj c)
  -> (DualVector (ToVObj a) ⊗ ToVObj c)
composeMorObj f g =
  ( (id ⊗^ unitLunit @(ToVObj c))
      . (id ⊗^ (arr (LinearFunction (cupUnfusedObj @b)) ⊗^ id))
      . (id ⊗^ lassocMap @(ToVObj b) @(DualVector (ToVObj b)) @(ToVObj c))
      . rassocMap
          @(DualVector (ToVObj a))
          @(ToVObj b)
          @(DualVector (ToVObj b) ⊗ ToVObj c)
  )
    $ (f ⊗ g)

--------------------------------------------------------------------------------
-- Category \/ monoidal structure: HomUnfused (complete)
--------------------------------------------------------------------------------

instance Category HomUnfused where
  type Object HomUnfused a = KnownToVObj a

  id :: forall a. Object HomUnfused a => HomUnfused a a
  id = HomUnfused (idMorObj @a)

  (.)
    :: forall a b c
     . (Object HomUnfused a, Object HomUnfused b, Object HomUnfused c)
    => HomUnfused b c
    -> HomUnfused a b
    -> HomUnfused a c
  HomUnfused g . HomUnfused f =
    HomUnfused (composeMorObj @a @b @c f g)

instance PFunctor FObj.Tensor HomUnfused HomUnfused where
  first
    :: forall a b c
     . ( Object HomUnfused a
       , Object HomUnfused b
       , Object HomUnfused c
       , Object HomUnfused (FObj.Tensor a c)
       , Object HomUnfused (FObj.Tensor b c)
       )
    => HomUnfused a b
    -> HomUnfused (FObj.Tensor a c) (FObj.Tensor b c)
  first (HomUnfused f) =
    let m :: ToVObj (FObj.Tensor a c) +> ToVObj (FObj.Tensor b c)
        m = (fromTensor -+$=> f) ⊗^ id
     in HomUnfused (asTensor -+$=> m)

instance QFunctor FObj.Tensor HomUnfused HomUnfused where
  second
    :: forall a b c
     . ( Object HomUnfused a
       , Object HomUnfused b
       , Object HomUnfused c
       , Object HomUnfused (FObj.Tensor c a)
       , Object HomUnfused (FObj.Tensor c b)
       )
    => HomUnfused a b
    -> HomUnfused (FObj.Tensor c a) (FObj.Tensor c b)
  second (HomUnfused g) =
    let m :: ToVObj (FObj.Tensor c a) +> ToVObj (FObj.Tensor c b)
        m = id ⊗^ (fromTensor -+$=> g)
     in HomUnfused (asTensor -+$=> m)

-- | @bimap f g@ is the Kronecker product of the underlying linear maps,
-- packed Dual-left: @(unpack f) ⊗^ (unpack g)@.
instance Bifunctor FObj.Tensor HomUnfused HomUnfused HomUnfused where
  bimap
    :: forall a b c d
     . ( Object HomUnfused a
       , Object HomUnfused b
       , Object HomUnfused c
       , Object HomUnfused d
       , Object HomUnfused (FObj.Tensor a c)
       , Object HomUnfused (FObj.Tensor b d)
       )
    => HomUnfused a b
    -> HomUnfused c d
    -> HomUnfused (FObj.Tensor a c) (FObj.Tensor b d)
  bimap (HomUnfused f) (HomUnfused g) =
    let m :: ToVObj (FObj.Tensor a c) +> ToVObj (FObj.Tensor b d)
        m = (fromTensor -+$=> f) ⊗^ (fromTensor -+$=> g)
     in HomUnfused (asTensor -+$=> m)

-- | Object associator is linearmap @α@ (Kronecker reassociation), packed as Hom.
instance Associative HomUnfused FObj.Tensor where
  associate
    :: forall a b c
     . ( Object HomUnfused a
       , Object HomUnfused b
       , Object HomUnfused c
       , Object HomUnfused (FObj.Tensor a b)
       , Object HomUnfused (FObj.Tensor b c)
       , Object HomUnfused (FObj.Tensor (FObj.Tensor a b) c)
       , Object HomUnfused (FObj.Tensor a (FObj.Tensor b c))
       )
    => HomUnfused (FObj.Tensor (FObj.Tensor a b) c) (FObj.Tensor a (FObj.Tensor b c))
  associate =
    HomUnfused
      ( asTensor -+$=>
          (rassocMap @(ToVObj a) @(ToVObj b) @(ToVObj c))
      )

  disassociate
    :: forall a b c
     . ( Object HomUnfused a
       , Object HomUnfused b
       , Object HomUnfused c
       , Object HomUnfused (FObj.Tensor a b)
       , Object HomUnfused (FObj.Tensor b c)
       , Object HomUnfused (FObj.Tensor (FObj.Tensor a b) c)
       , Object HomUnfused (FObj.Tensor a (FObj.Tensor b c))
       )
    => HomUnfused (FObj.Tensor a (FObj.Tensor b c)) (FObj.Tensor (FObj.Tensor a b) c)
  disassociate =
    HomUnfused
      ( asTensor -+$=>
          (lassocMap @(ToVObj a) @(ToVObj b) @(ToVObj c))
      )

instance Monoidal HomUnfused FObj.Tensor where
  type Id HomUnfused FObj.Tensor = 'FObj.Atom 0

  idl
    :: forall a
     . ( Object HomUnfused a
       , Object HomUnfused ('FObj.Atom 0)
       , Object HomUnfused (FObj.Tensor ('FObj.Atom 0) a)
       )
    => HomUnfused (FObj.Tensor ('FObj.Atom 0) a) a
  idl =
    HomUnfused (asTensor -+$=> (unitLunit @(ToVObj a)))

  idr
    :: forall a
     . ( Object HomUnfused a
       , Object HomUnfused ('FObj.Atom 0)
       , Object HomUnfused (FObj.Tensor a ('FObj.Atom 0))
       )
    => HomUnfused (FObj.Tensor a ('FObj.Atom 0)) a
  idr =
    HomUnfused (asTensor -+$=> (unitRunit @(ToVObj a)))

  coidl
    :: forall a
     . ( Object HomUnfused a
       , Object HomUnfused ('FObj.Atom 0)
       , Object HomUnfused (FObj.Tensor ('FObj.Atom 0) a)
       )
    => HomUnfused a (FObj.Tensor ('FObj.Atom 0) a)
  coidl =
    HomUnfused (asTensor -+$=> (unitLcounit @(ToVObj a)))

  coidr
    :: forall a
     . ( Object HomUnfused a
       , Object HomUnfused ('FObj.Atom 0)
       , Object HomUnfused (FObj.Tensor a ('FObj.Atom 0))
       )
    => HomUnfused a (FObj.Tensor a ('FObj.Atom 0))
  coidr =
    HomUnfused (asTensor -+$=> (unitRcounit @(ToVObj a)))

instance Braided HomUnfused FObj.Tensor where
  braid
    :: forall a b
     . ( Object HomUnfused a
       , Object HomUnfused b
       , Object HomUnfused (FObj.Tensor a b)
       , Object HomUnfused (FObj.Tensor b a)
       )
    => HomUnfused (FObj.Tensor a b) (FObj.Tensor b a)
  braid =
    let m :: ToVObj (FObj.Tensor a b) +> ToVObj (FObj.Tensor b a)
        m = swapMap @(ToVObj a) @(ToVObj b)
     in HomUnfused (asTensor -+$=> m)

-- | Object constraint for fused Hom: 'Obj' with a known identity on 'ObjRep'.
class KnownHomFused (a :: Obj Nat) where
  idHomFusedVal :: RepV (FuseRep (ObjRep a) (ObjRep a))

-- | Identity endomorphism on a leaf: singlet (@root = 0@) channel = 1, else 0.
--
-- Interim singlet walk (paired with 'cup'). True fused η once channel-native F
-- lands.
idHomI
  :: forall j
   . ( KnownNat j
     , KnownFTrees (FuseRep '[ 'I j] '[ 'I j])
     )
  => RepV (FuseRep '[ 'I j] '[ 'I j])
idHomI = go (fTreesSing @(FuseRep '[ 'I j] '[ 'I j]))
  where
    go :: forall ts. SFTrees ts -> RepV ts
    go SFTreesNil = RNil
    go (SFTreesCons (t :: SFTree u) rest) =
      case t of
        SFrom @d _l _r ->
          case sameNat (Proxy @d) (Proxy @0) of
            Just Refl -> RCons @u (konst 1) (go rest)
            Nothing -> RCons @u zeroV (go rest)
        SI {} ->
          error "idHomI: expected Hom From channels"

-- | Simple atom: identity via 'idHomI' (@ObjSpineSU2 ('Atom j) ~ '[ '(j,1)]@).
instance
  ( KnownNat j
  , KnownFTrees (FuseRep '[ 'I j] '[ 'I j])
  , ObjSpineSU2 ('FObj.Atom j) ~ '[ '(j, 1)]
  , ObjRep ('FObj.Atom j) ~ '[ 'I j]
  ) =>
  KnownHomFused ('FObj.Atom j)
  where
  idHomFusedVal = idHomI @j

-- Category \/ monoidal structure: HomUnfused (complete). HomFused Category lives
-- with the tree compose ladder (see 'composeHomFused').

--------------------------------------------------------------------------------
-- Fused Hom compose: five Mac Lane morphisms (genealogy Hom; left ≅ dual)
--
--   f ⊗ g
--     ─ F ─►     a* ⊗ (b ⊗ (b* ⊗ c))
--     ─ id⊗F ─►  a* ⊗ ((b ⊗ b*) ⊗ c)
--     ─ id⊗(ε⊗id) ─►  a* ⊗ (Unit ⊗ c)
--     ─ id⊗λ ─►  a* ⊗ c
--------------------------------------------------------------------------------

-- | Step 1: @f ⊗ g@ is 'fuseRepTerm' (inlined at 'composeHomTrees').
-- Step 2: outer F — @(a*⊗b) ⊗ (b*⊗c) → a* ⊗ (b ⊗ (b*⊗c))@.
--
-- Discharged by 'CanFmoveOuterHom' (leaf instance → 'fmoveOuterHomLeaves').
-- ('fmoveInnerHom' is the subsequent @id ⊗ F@ via 'fuseMapRight' 'fmoveInvTrees'.)

-- | Step 3: @id ⊗ F@ — @a* ⊗ (b ⊗ (b*⊗c)) → a* ⊗ ((b ⊗ b*) ⊗ c)@.
--
-- Right factor: @FuseRep b (FuseRep b c) → FuseRep (FuseRep b b) c@ via 'fmoveInvTrees'.
fmoveInnerHom
  :: forall a b c
   . ( KnownFTrees a
     , KnownFTrees (FuseRep b (FuseRep b c))
     , KnownFTrees (FuseRep (FuseRep b b) c)
     , KnownFTrees (FuseRep a (FuseRep b (FuseRep b c)))
     , KnownFTrees (FuseRep a (FuseRep (FuseRep b b) c))
     , CanFmoveTrees b b c
     )
  => RepV (FuseRep a (FuseRep b (FuseRep b c)))
  -> RepV (FuseRep a (FuseRep (FuseRep b b) c))
fmoveInnerHom =
  fuseMapRight
    @a
    @(FuseRep b (FuseRep b c))
    @(FuseRep (FuseRep b b) c)
    (fmoveInvTrees @b @b @c)

-- | Step 4: @id ⊗ (cup ⊗ id)@ — Unit remains in the type.
cupTensorIdHom
  :: forall a b c
   . ( KnownFTrees a
     , KnownFTrees b
     , KnownFTrees c
     , KnownFTrees (FuseRep b b)
     , KnownFTrees Unit
     , KnownFTrees (FuseRep (FuseRep b b) c)
     , KnownFTrees (FuseRep Unit c)
     , KnownFTrees (FuseRep a (FuseRep (FuseRep b b) c))
     , KnownFTrees (FuseRep a (FuseRep Unit c))
     , KnownFTrees (FuseRep b b)
     )
  => RepV (FuseRep a (FuseRep (FuseRep b b) c))
  -> RepV (FuseRep a (FuseRep Unit c))
cupTensorIdHom =
  fuseMapRight
    @a
    @(FuseRep (FuseRep b b) c)
    @(FuseRep Unit c)
    ( fuseMapLeft
        @(FuseRep b b)
        @Unit
        @c
        (cup @b)
    )

-- | Evaluation @ε : b ⊗ b* → 𝟙@ on genealogy Hom (@FuseRep b b@, dual≅primal).
--
-- Interim: singlet walk on 'SFTrees' (scale by FS·dim). True η/ε morphisms once
-- typed per-channel F replaces Fusion.SU2 flats (blocker: channel morphisms on
-- @C (d+1)@).
cup
  :: forall b
   . KnownFTrees (FuseRep b b)
  => RepV (FuseRep b b)
  -> RepV Unit
cup bb =
  RCons @('I 0) (konst (cupHomTreesScalar @(FuseRep b b) bb)) RNil
  where
    -- Singlet walk via 'SFTrees': @sameNat@ refines @j ~ 0@ so payloads stay @C 1@.
    cupHomTreesScalar
      :: forall ts
       . KnownFTrees ts
      => RepV ts
      -> Complex Double
    cupHomTreesScalar = go (fTreesSing @ts)
      where
        go :: forall ts'. SFTrees ts' -> RepV ts' -> Complex Double
        go SFTreesNil RNil = 0
        go (SFTreesCons t rest) (RCons v rs) =
          case t of
            SI @j ->
              case sameNat (Proxy @j) (Proxy @0) of
                Just Refl -> (konst 1 <.> v) + go rest rs
                Nothing -> go rest rs
            SFrom @j l _r ->
              case sameNat (Proxy @j) (Proxy @0) of
                Just Refl ->
                  su2CupFactor (rootLab l) * (konst 1 <.> v) + go rest rs
                Nothing -> go rest rs

    -- Frobenius–Schur cup factor @FS(j)·dim(j)@ (@tj = 2j@).
    su2CupFactor :: Int -> Complex Double
    su2CupFactor tj =
      let fs = if even tj then 1 else -1
          dim = fromIntegral (tj + 1) :: Double
       in (fs * dim) :+ 0

-- | Step 5: @id ⊗ λ@ — @a* ⊗ (Unit ⊗ c) → a* ⊗ c@ (not type-level absorption).
unitorHom
  :: forall a c
   . ( KnownFTrees a
     , KnownFTrees c
     , KnownFTrees (FuseRep Unit c)
     , KnownFTrees (FuseRep a (FuseRep Unit c))
     , KnownFTrees (FuseRep a c)
     , UnitorCodomain (FuseRep Unit c) ~ c
     )
  => RepV (FuseRep a (FuseRep Unit c))
  -> RepV (FuseRep a c)
unitorHom =
  fuseMapRight @a @(FuseRep Unit c) @c (unitor @c)

-- | Left unitor on fusion trees: @Unit ⊗ c → c@ (drop @'I 0@ left child).
--
-- For each @t@ in @c@, @FuseTrees ('I 0) t = '[ 'From (Root t) '( 'I 0, t) ]@
-- (SU(2): @0 ⊗ j = j@); payloads are already the root irrep of @t@.
unitor
  :: forall c
   . ( KnownFTrees (FuseRep Unit c)
     , UnitorCodomain (FuseRep Unit c) ~ c
     )
  => RepV (FuseRep Unit c)
  -> RepV c
unitor = go (fTreesSing @(FuseRep Unit c))
  where
    -- @sameNat@ refines left child to @'I 0@; 'UnitorCodomain' drops it.
    go
      :: forall uc
       . SFTrees uc
      -> RepV uc
      -> RepV (UnitorCodomain uc)
    go SFTreesNil RNil = RNil
    go (SFTreesCons t rest) (RCons v rs) =
      case t of
        SFrom @j l r ->
          case l of
            SI @zj ->
              case sameNat (Proxy @zj) (Proxy @0) of
                Just Refl ->
                  case r of
                    SI @rj ->
                      case sameNat (Proxy @rj) (Proxy @j) of
                        Just Refl ->
                          RCons @('I rj) v (go rest rs)
                        Nothing ->
                          error "unitor: root mismatch after 0⊗t"
                    SFrom @rj @rl @rr _l _r ->
                      case sameNat (Proxy @rj) (Proxy @j) of
                        Just Refl ->
                          RCons @('From rj '(rl, rr)) v (go rest rs)
                        Nothing ->
                          error "unitor: root mismatch after 0⊗t"
                Nothing ->
                  error "unitor: expected left child 'I 0"
            SFrom {} ->
              error "unitor: expected left child 'I 0"
        SI {} ->
          error "unitor: expected From from FuseRep Unit"

-- | Fused Hom compose as the five Mac Lane morphisms.
composeHomTrees
  :: forall a b c
   . ( KnownFTrees (FuseRep a b)
     , KnownFTrees (FuseRep b c)
     , FuseRepTermC (FuseRep a b) (FuseRep b c)
     , KnownFTrees a
     , KnownFTrees b
     , KnownFTrees c
     , KnownFTrees (FuseRep b b)
     , KnownFTrees Unit
     , KnownFTrees (FuseRep b (FuseRep b c))
     , KnownFTrees (FuseRep (FuseRep b b) c)
     , KnownFTrees (FuseRep Unit c)
     , KnownFTrees (FuseRep a (FuseRep b (FuseRep b c)))
     , KnownFTrees (FuseRep a (FuseRep (FuseRep b b) c))
     , KnownFTrees (FuseRep a (FuseRep Unit c))
     , KnownFTrees (FuseRep a c)
     , CanFmoveOuterHom a b c
     , CanFmoveTrees b b c
     , UnitorCodomain (FuseRep Unit c) ~ c
     )
  => RepV (FuseRep a b)
  -> RepV (FuseRep b c)
  -> RepV (FuseRep a c)
composeHomTrees f g =
  unitorHom @a @c
    ( cupTensorIdHom @a @b @c
        ( fmoveInnerHom @a @b @c
            ( fmoveOuterHom @a @b @c
                (fuseRepTerm @(FuseRep a b) @(FuseRep b c) f g)
            )
        )
    )

--------------------------------------------------------------------------------
-- HomFused: RepV-backed fused Hom
--------------------------------------------------------------------------------

-- | SU(2) dual iso on spin-½: @ε⁻¹ = [[0,-1],[1,0]]@ (maps Euclidean Dual≅V
-- name of id to the CG singlet convention used by fused Hom).
su2DualIsoHalfInv :: C 2 +> C 2
su2DualIsoHalfInv =
  arr . LinearFunction $ \v ->
    let [a, b] = VS.toList (toArray v)
     in unsafeFromArray (VS.fromList [-b, a])

-- | Forgetful map @HomFused ⇒ HomUnfused@ on spin-½ atoms.
--
-- CG-unfuse channels, apply the FS dual iso on the left (dual) leg, scale by
-- @√dim = √2@ so fused id densifies to Euclidean id. Preserves compose on the
-- intertwiner (singlet) sector — see 'checkForgetHomInterCompose111'. Full
-- End/@HomFused@ functoriality for triplet channels is still open.
forgetHomFusedHalf
  :: HomFused ('FObj.Atom 1) ('FObj.Atom 1)
  -> HomUnfused ('FObj.Atom 1) ('FObj.Atom 1)
forgetHomFusedHalf (HomFused r) =
  let u = unfuseTrees @('I 1) @('I 1) r
      mid = (su2DualIsoHalfInv ⊗^ (id :: C 2 +> C 2)) $ u
      packed = (sqrt 2 :+ 0) *^ mid
      m = fromTensor -+$=> packed :: C 2 +> C 2
   in HomUnfused (asTensor -+$=> m)

-- | 'HomFused' compose via the five Mac Lane morphisms ('composeHomTrees')
-- on 'ObjRep'-expanded leaf reps.
composeHomFused
  :: forall a b c
   . ( KnownFTrees (FuseRep (ObjRep a) (ObjRep b))
     , KnownFTrees (FuseRep (ObjRep b) (ObjRep c))
     , FuseRepTermC (FuseRep (ObjRep a) (ObjRep b)) (FuseRep (ObjRep b) (ObjRep c))
     , KnownFTrees (ObjRep a)
     , KnownFTrees (ObjRep b)
     , KnownFTrees (ObjRep c)
     , KnownFTrees (FuseRep (ObjRep b) (ObjRep b))
     , KnownFTrees Unit
     , KnownFTrees (FuseRep (ObjRep b) (FuseRep (ObjRep b) (ObjRep c)))
     , KnownFTrees (FuseRep (FuseRep (ObjRep b) (ObjRep b)) (ObjRep c))
     , KnownFTrees (FuseRep Unit (ObjRep c))
     , KnownFTrees (FuseRep (ObjRep a) (FuseRep (ObjRep b) (FuseRep (ObjRep b) (ObjRep c))))
     , KnownFTrees (FuseRep (ObjRep a) (FuseRep (FuseRep (ObjRep b) (ObjRep b)) (ObjRep c)))
     , KnownFTrees (FuseRep (ObjRep a) (FuseRep Unit (ObjRep c)))
     , KnownFTrees (FuseRep (ObjRep a) (ObjRep c))
     , CanFmoveOuterHom (ObjRep a) (ObjRep b) (ObjRep c)
     , CanFmoveTrees (ObjRep b) (ObjRep b) (ObjRep c)
     , UnitorCodomain (FuseRep Unit (ObjRep c)) ~ ObjRep c
     )
  => HomFused b c
  -> HomFused a b
  -> HomFused a c
composeHomFused (HomFused g) (HomFused f) =
  HomFused (composeHomTrees @(ObjRep a) @(ObjRep b) @(ObjRep c) f g)

instance Category HomFused where
  type Object HomFused a = KnownHomFused a

  id :: forall a. Object HomFused a => HomFused a a
  id = HomFused (idHomFusedVal @a)

  -- @(.)@ needs the five Mac Lane steps on @a,b,c@, which 'Object' alone does
  -- not imply (constraints are triple-indexed). Named ladder: 'composeHomFused'.
  (.) = undefined

--------------------------------------------------------------------------------
-- HomInter: trivial sector of fused Hom (same Mac Lane compose)
--------------------------------------------------------------------------------

-- | Identity intertwiner: trivial channels of 'idHomFusedVal'.
idHomInterVal
  :: forall a
   . ( KnownHomFused a
     , KnownFTrees (FuseRep (ObjRep a) (ObjRep a))
     , FilterTrivialC (FuseRep (ObjRep a) (ObjRep a))
     )
  => RepV (FilterTrivial (FuseRep (ObjRep a) (ObjRep a)))
idHomInterVal =
  filterTrivialRepV @(FuseRep (ObjRep a) (ObjRep a)) (idHomFusedVal @a)

-- | 'HomInter' compose: embed → 'composeHomTrees' → filter (same as 'HomFused').
composeHomInter
  :: forall a b c
   . ( KnownFTrees (FuseRep (ObjRep a) (ObjRep b))
     , KnownFTrees (FuseRep (ObjRep b) (ObjRep c))
     , KnownFTrees (FuseRep (ObjRep a) (ObjRep c))
     , FilterTrivialC (FuseRep (ObjRep a) (ObjRep b))
     , FilterTrivialC (FuseRep (ObjRep b) (ObjRep c))
     , FilterTrivialC (FuseRep (ObjRep a) (ObjRep c))
     , FuseRepTermC
         (FuseRep (ObjRep a) (ObjRep b))
         (FuseRep (ObjRep b) (ObjRep c))
     , KnownFTrees (ObjRep a)
     , KnownFTrees (ObjRep b)
     , KnownFTrees (ObjRep c)
     , KnownFTrees (FuseRep (ObjRep b) (ObjRep b))
     , KnownFTrees Unit
     , KnownFTrees (FuseRep (ObjRep b) (FuseRep (ObjRep b) (ObjRep c)))
     , KnownFTrees (FuseRep (FuseRep (ObjRep b) (ObjRep b)) (ObjRep c))
     , KnownFTrees (FuseRep Unit (ObjRep c))
     , KnownFTrees
         ( FuseRep
             (ObjRep a)
             (FuseRep (ObjRep b) (FuseRep (ObjRep b) (ObjRep c)))
         )
     , KnownFTrees
         ( FuseRep
             (ObjRep a)
             (FuseRep (FuseRep (ObjRep b) (ObjRep b)) (ObjRep c))
         )
     , KnownFTrees (FuseRep (ObjRep a) (FuseRep Unit (ObjRep c)))
     , CanFmoveOuterHom (ObjRep a) (ObjRep b) (ObjRep c)
     , CanFmoveTrees (ObjRep b) (ObjRep b) (ObjRep c)
     , UnitorCodomain (FuseRep Unit (ObjRep c)) ~ ObjRep c
     )
  => HomInter b c
  -> HomInter a b
  -> HomInter a c
composeHomInter (HomInter g) (HomInter f) =
  HomInter $
    filterTrivialRepV @(FuseRep (ObjRep a) (ObjRep c)) $
      composeHomTrees @(ObjRep a) @(ObjRep b) @(ObjRep c)
        (embedTrivialRepV @(FuseRep (ObjRep a) (ObjRep b)) f)
        (embedTrivialRepV @(FuseRep (ObjRep b) (ObjRep c)) g)

instance Category HomInter where
  type Object HomInter a =
    ( KnownHomFused a
    , KnownFTrees (FuseRep (ObjRep a) (ObjRep a))
    , FilterTrivialC (FuseRep (ObjRep a) (ObjRep a))
    )

  id :: forall a. Object HomInter a => HomInter a a
  id = HomInter (idHomInterVal @a)

  -- Same as 'HomFused': use 'composeHomInter' (needs Mac Lane constraints).
  (.) = undefined

